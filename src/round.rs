use crate::gcd::gcd;

/// Budget bound: |num| and den must each be ≤ BOUND.
pub(crate) const BOUND: u64 = (1u64 << 62) - 1;

/// Rounding direction for budget overflow.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Dir {
    /// Result ≤ exact value (toward −∞).
    Down,
    /// Result ≥ exact value (toward +∞).
    Up,
    /// Round to nearest, ties away from zero.
    Nearest,
}

/// Returns true if both |num| and den fit in the I2 budget.
pub(crate) fn fits_budget(num: i128, den: i128) -> bool {
    debug_assert!(den > 0);
    num.unsigned_abs() <= BOUND as u128 && den as u128 <= BOUND as u128
}

/// Dyadic snap rounding: given a reduced fraction num/den (den > 0) that
/// does NOT fit in I2, produce (rnum, rden) that does, with error bound
/// |rnum/rden - num/den| ≤ 2^{-60} · max(1, |num/den|).
///
/// Algorithm: approximate num/den as k / 2^s where s is chosen so |k| ≤ BOUND
/// and 2^s ≤ BOUND, then GCD-reduce k / 2^s.
///
/// Verus obligation V4: R1–R4.
pub(crate) fn round_to_budget(num: i128, den: i128, dir: Dir) -> (i64, i64) {
    debug_assert!(den > 0);
    debug_assert!(!fits_budget(num, den));

    if num == 0 {
        return (0, 1);
    }

    let sign: i128 = if num > 0 { 1 } else { -1 };
    let p = num.unsigned_abs();
    let q = den as u128;

    let s = choose_shift(p, q);

    let k = div_shifted(p, q, s, sign, dir);

    let den_pow = 1u64 << s;

    if k == 0 {
        return (0, 1);
    }

    let k_abs = k.unsigned_abs() as u64;
    let g = gcd(k_abs, den_pow);
    let rnum = (k.signum() * (k_abs / g) as i64) as i64;
    let rden = (den_pow / g) as i64;

    debug_assert!(rnum.unsigned_abs() <= BOUND);
    debug_assert!((rden as u64) <= BOUND);
    debug_assert!(rden > 0);

    (rnum, rden)
}

/// Choose the shift s for dyadic snap.
///
/// We want: k = round(p * 2^s / q) with |k| ≤ BOUND.
/// This means 2^s ≤ BOUND * q / p (approximately).
/// Also s ≤ 61 (so 2^s ≤ 2^61 < BOUND).
///
/// For the error bound B ≥ 60: s ≥ 60 - floor(log2(p/q)).
fn choose_shift(p: u128, q: u128) -> u32 {
    debug_assert!(p > 0);
    debug_assert!(q > 0);

    let bits_p = 128 - p.leading_zeros(); // = floor(log2(p)) + 1
    let bits_q = 128 - q.leading_zeros();

    // floor(log2(p/q)) ≈ bits_p - bits_q (within ±1)
    // We want s such that p * 2^s / q ≈ 2^61 (fits in 62 bits with margin).
    // So s ≈ 61 + bits_q - bits_p.
    // Clamp to [0, 61].
    let s_approx = 61i32 + bits_q as i32 - bits_p as i32;
    let s = s_approx.clamp(0, 61) as u32;

    // Verify by computing k at this s. If |k| > BOUND, decrease s.
    // We check cheaply: p >> (bits_p - 1) * 2^s / (q >> (bits_q - 1)) should be ~ 2^61.
    // But it's simpler to just compute and adjust in div_shifted if needed.
    s
}

/// Compute round(p * 2^s / q) * sign, using long division to avoid i128 overflow.
///
/// p, q are unsigned magnitudes (q > 0). sign is ±1.
/// dir controls rounding of the final remainder.
///
/// Returns the result as i64 (guaranteed to fit by choice of s, with possible
/// one-step adjustment).
fn div_shifted(p: u128, q: u128, mut s: u32, sign: i128, dir: Dir) -> i64 {
    let (k, remainder) = long_div_shifted(p, q, s);

    // Check |k| ≤ BOUND; if not, decrease s and retry
    if k > BOUND as u128 {
        if s == 0 {
            // Value is simply too large; snap to the nearest representable.
            // This shouldn't happen with valid I2 inputs to arithmetic ops.
            // Defensive: return BOUND with correct sign.
            return if sign > 0 { BOUND as i64 } else { -(BOUND as i64) };
        }
        s -= 1;
        let (k2, remainder2) = long_div_shifted(p, q, s);
        return apply_rounding(k2, remainder2, q, sign, dir);
    }

    apply_rounding(k, remainder, q, sign, dir)
}

/// Long division: compute (floor(p * 2^s / q), remainder).
///
/// Uses bit-by-bit long division so that intermediates never exceed u128.
/// The quotient is floor(p * 2^s / q), and remainder satisfies:
///   p * 2^s = quotient * q + remainder, with 0 ≤ remainder < q.
fn long_div_shifted(p: u128, q: u128, s: u32) -> (u128, u128) {
    debug_assert!(q > 0);

    let p_bits = if p == 0 { 0 } else { 128 - p.leading_zeros() };
    let total_bits = p_bits + s;

    let mut quotient: u128 = 0;
    let mut remainder: u128 = 0;

    for j in 0..total_bits {
        let bit = if j < p_bits {
            (p >> (p_bits - 1 - j)) & 1
        } else {
            0
        };

        remainder = remainder * 2 + bit;
        quotient *= 2;
        if remainder >= q {
            quotient += 1;
            remainder -= q;
        }
    }

    (quotient, remainder)
}

/// Apply rounding based on Dir to the truncated quotient k = floor(|exact|*2^s / q).
fn apply_rounding(k: u128, remainder: u128, q: u128, sign: i128, dir: Dir) -> i64 {
    let round_up = match dir {
        Dir::Nearest => remainder * 2 >= q,
        Dir::Up => {
            if sign > 0 {
                remainder > 0
            } else {
                false
            }
        }
        Dir::Down => {
            if sign < 0 {
                remainder > 0
            } else {
                false
            }
        }
    };

    let k_rounded = if round_up { k + 1 } else { k };

    // Safety: k_rounded should be ≤ BOUND. If the +1 from rounding pushes it over,
    // we accept BOUND+1 ≈ 2^62 which is still within i64 range.
    debug_assert!(k_rounded <= BOUND as u128 + 1);

    let magnitude = k_rounded.min(BOUND as u128) as i64;

    if sign > 0 {
        magnitude
    } else {
        -magnitude
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fits_budget_basic() {
        assert!(fits_budget(0, 1));
        assert!(fits_budget(1, 1));
        assert!(fits_budget(BOUND as i128, BOUND as i128));
        assert!(fits_budget(-(BOUND as i128), BOUND as i128));
        assert!(!fits_budget(BOUND as i128 + 1, 1));
        assert!(!fits_budget(1, BOUND as i128 + 1));
    }

    #[test]
    fn round_small_value() {
        // 1 / (2^63) doesn't fit (den too large). Should round to something small.
        let big_den: i128 = 1i128 << 63;
        let (rn, rd) = round_to_budget(1, big_den, Dir::Nearest);
        assert!(rn.unsigned_abs() <= BOUND);
        assert!((rd as u64) <= BOUND);
        assert!(rd > 0);
        // The exact value is ~1.08e-19; rounded to 0 is acceptable
        // (error < 2^-60 ≈ 8.67e-19 > 1.08e-19)
    }

    #[test]
    fn round_near_one() {
        // A value near 1 with a huge denominator
        let big = (1i128 << 63) + 1;
        let (rn, rd) = round_to_budget(big, 1i128 << 63, Dir::Nearest);
        assert!(rn.unsigned_abs() <= BOUND);
        assert!((rd as u64) <= BOUND);
        // Should be very close to 1
        let approx = rn as f64 / rd as f64;
        assert!((approx - 1.0).abs() < 1e-10);
    }

    #[test]
    fn round_preserves_direction() {
        let num: i128 = (1i128 << 63) + 7;
        let den: i128 = (1i128 << 63) - 3;

        let (dn, dd) = round_to_budget(num, den, Dir::Down);
        let (un, ud) = round_to_budget(num, den, Dir::Up);

        let down_val = dn as f64 / dd as f64;
        let up_val = un as f64 / ud as f64;
        let exact_val = num as f64 / den as f64;

        assert!(down_val <= exact_val + 1e-15);
        assert!(up_val >= exact_val - 1e-15);
    }
}
