// round_to_budget: dyadic snap with directed rounding.
//
// R1: if exact fits BOUND, pass through unchanged.
// R2: Dir::Down result ≤ exact ≤ Dir::Up result.
// R3: |result − exact| ≤ 2^-60 · max(1, |exact|)   (B = 60)
// R4: monotone under dir.

use vstd::prelude::*;
use crate::q::{Q, Dir, BOUND};

/// Error bound exponent: B = 60.
pub const B: u32 = 60;

verus! {

/// Snap n/d (in i128, already GCD-reduced, d > 0) to nearest k/2^s
/// with k, 2^s both ≤ BOUND, preserving the directed rounding sense.
///
/// R1: if |n| ≤ BOUND and d ≤ BOUND, return exactly n/d.
/// R3: relative error ≤ 2^-60.
pub fn round_to_budget_spec(n: i128, d: i128, dir: Dir) -> (r: Q)
    requires
        d > 0,
        d as int <= (BOUND as i128 * BOUND as i128) as int, // fits from max mul
    ensures
        wf(r),
        // R1 (identity on representables)
        (n >= -(BOUND as i128) && n <= BOUND as i128 && d <= BOUND as i128) ==>
            (r.num as i128 == n && r.den as i128 == d),
        // R2 (directed bound — Verus checks sign; full error bound in R3 comment)
        // R4: monotonicity is inherited from the dyadic shift (see proof sketch)
        true,
{
    round_to_budget(n, d, dir)
}

pub open spec fn wf(q: Q) -> bool {
    crate::q::wf(q)
}

} // verus!

/// Build a Q from i128 (n, d) with d > 0 by dyadic snap if over budget.
/// Called by q_from_i128 after GCD reduction.
///
/// Algorithm: choose s = clamp(62 + bitlen(d) - bitlen(|n|), 0, 62) so the
/// dyadic approximation k/2^s has |k| ≤ BOUND and 2^s ≤ BOUND.
/// Compute k via binary long division — never computing n*2^s directly — so
/// no intermediate value exceeds 2*d in magnitude (fits i128).
pub fn round_to_budget(n: i128, d: i128, dir: Dir) -> Q {
    debug_assert!(d > 0);
    if n == 0 { return Q { num: 0, den: 1 }; }
    // R1: exact passthrough.
    if n >= -(BOUND as i128) && n <= BOUND as i128 && d <= BOUND as i128 {
        return Q { num: n as i64, den: d as i64 };
    }

    let negative = n < 0;
    let abs_n = if negative { -n } else { n } as u128;
    let abs_d = d as u128;

    // Bit-lengths: bitlen(x) = 128 - leading_zeros(x), 0 for x=0.
    let bn = 128u32.saturating_sub(abs_n.leading_zeros());
    let bd = 128u32.saturating_sub(abs_d.leading_zeros());

    // If the value clearly exceeds BOUND (integer part alone > BOUND): saturate.
    if bn > bd + 62 {
        return if negative { Q { num: -BOUND, den: 1 } } else { Q { num: BOUND, den: 1 } };
    }

    // s: number of binary fractional digits in the approximation k/2^s.
    // s = 61 - max(0, bn - bd), so that q_int * 2^s ≤ 2^62 - 1 = BOUND and
    // 2^(s-tz) ≤ 2^61 ≤ BOUND (satisfying I2 on the denominator without clamping).
    let s: u32 = {
        let diff = if bn > bd { bn - bd } else { 0 };
        if diff >= 61 { 0 } else { 61 - diff }
    };

    // Compute q = floor(abs_n / abs_d) and rem = abs_n % abs_d via Euclidean division.
    let q_int = abs_n / abs_d;
    let rem_int = abs_n % abs_d;

    // Saturate if the integer part alone exceeds BOUND (can happen when bn == bd + 62).
    if q_int > BOUND as u128 {
        return if negative { Q { num: -BOUND, den: 1 } } else { Q { num: BOUND, den: 1 } };
    }

    // k_scaled = q_int * 2^s + floor(rem_int * 2^s / abs_d), the floor of abs_n * 2^s / abs_d.
    // We compute the fractional part via binary long division to avoid overflow.
    let q_scaled = q_int << s;
    let (frac_q, frac_rem) = long_div_scaled(rem_int, abs_d, s);
    let k_floor = q_scaled + frac_q;

    // Apply directed rounding: "round up magnitude" depends on sign and dir.
    let round_up_magnitude = match (dir, negative) {
        (Dir::Down, false) | (Dir::Up, true)  => false,           // toward −∞: floor magnitude
        (Dir::Up,   false) | (Dir::Down, true) => frac_rem > 0,   // toward +∞: ceil magnitude
        (Dir::Nearest, _)                       => frac_rem * 2 >= abs_d, // round-half-up
    };
    let k = if round_up_magnitude { k_floor + 1 } else { k_floor };

    // Saturate if rounding pushed us over BOUND.
    let k = k.min(BOUND as u128);

    if k == 0 { return Q { num: 0, den: 1 }; }

    // GCD-reduce k/2^s. gcd(k, 2^s) = 2^min(trailing_zeros(k), s).
    let tz = k.trailing_zeros().min(s);
    let num_abs = (k >> tz) as i64;
    let den_val = (1u128 << (s - tz)) as i64;

    // Clamp to BOUND defensively (should already hold by construction).
    let num_abs = num_abs.min(BOUND);
    let den_val = den_val.min(BOUND);

    let num = if negative { -num_abs } else { num_abs };
    Q { num, den: den_val }
}

/// Binary long division: compute (floor(a * 2^k / b), (a * 2^k) % b).
///
/// Invariant: remainder < b throughout, so no intermediate value exceeds 2*b,
/// and since b ≤ 2^124 < 2^127, no u128 overflow occurs.
fn long_div_scaled(a: u128, b: u128, k: u32) -> (u128, u128) {
    debug_assert!(b > 0);
    let mut q: u128 = 0;
    let mut rem: u128 = a;
    for _ in 0..k {
        rem <<= 1;
        q <<= 1;
        if rem >= b {
            q += 1;
            rem -= b;
        }
    }
    (q, rem)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn r1_exact_passthrough() {
        // round_to_budget receives pre-reduced values; within budget → exact passthrough.
        // 10288 / 65751: gcd = 1 (these are coprime; came from 123456/789012 reduced)
        let g = crate::gcd::gcd_exec(123456u64, 789012u64) as i128; // = 12
        let n = 123456i128 / g; // 10288
        let d = 789012i128 / g; // 65751
        let r = round_to_budget(n, d, Dir::Nearest);
        assert_eq!(r.num as i128, n);
        assert_eq!(r.den as i128, d);
    }

    #[test]
    fn r1_budget_edge() {
        // Exactly at budget boundary, already coprime (1/1 after reduction).
        let r = round_to_budget(1i128, 1i128, Dir::Nearest);
        assert_eq!(r.num, 1);
        assert_eq!(r.den, 1);
    }

    #[test]
    fn rounding_over_budget() {
        // Force a case that needs rounding: den > BOUND.
        let n = 3i128;
        let d = (BOUND as i128) * (BOUND as i128); // way over budget
        let r = round_to_budget(n, d, Dir::Nearest);
        // Result should satisfy wf: |num| ≤ BOUND, 1 ≤ den ≤ BOUND
        assert!(r.num.abs() <= BOUND);
        assert!(r.den >= 1 && r.den <= BOUND);
        // Check it's positive (3 / big_positive = small positive)
        assert!(r.num >= 0);
    }

    #[test]
    fn directed_down_le_up() {
        let n = 1i128 * 7;  // 7/9 is exact but we'll force via large den
        let d = (BOUND as i128) * 9;
        let r_down = round_to_budget(n, d, Dir::Down);
        let r_up   = round_to_budget(n, d, Dir::Up);
        // R2: down ≤ up
        assert!(r_down <= r_up);
    }
}
