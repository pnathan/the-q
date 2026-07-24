//! Canonicalization and the directed-rounding contract (spec §3, obligation V4).
//!
//! Every public arithmetic op funnels its exact `i128` numerator/denominator
//! through [`from_exact_i128`]: if the gcd-reduced exact result already fits
//! the `I2` budget it is returned unchanged (**R1**, identity on
//! representables -- any computation whose exact values all fit the budget
//! is therefore end-to-end exact, with zero rounding). Otherwise
//! [`round_to_budget`] snaps it to the nearest (or directed) dyadic fraction
//! `k / 2^s` with `s` chosen so `k` and `2^s` both fit `I2`.
//!
//! ## The rounding algorithm (dyadic snap)
//!
//! Let `m = bitlen(|num|)`, `l = bitlen(den)` for the coprime, sign-normalized
//! exact pair. `m - l` approximates `log2(|value|)`. We choose the shift
//! `s = clamp(61 - (m - l), 0, 61)` so the scaled magnitude `|value| * 2^s`
//! lands near `2^61` -- one bit of headroom below the `I2` ceiling of
//! `2^62 - 1`, so a rounding carry never itself overflows the budget.
//!
//! The scaled magnitude is computed by **binary long division**
//! (`q0 = |num| / den`, then `s` more bits by repeatedly doubling the
//! remainder), never by shifting `|num|` directly -- `|num|` can already be
//! up to ~2^125 bits wide (see the overflow table in the spec / crate
//! README), and `|num| << 61` would overflow `i128` long before the
//! division ever runs. The remainder is always `< den`, so each doubling
//! step is bounded by `2 * den`, which is safe in `u128` for any `den` that
//! itself fits `i128`.
//!
//! `R3` (error `<= 2^-60 * max(1, |exact|)`) follows from `s >= 60` whenever
//! the value's magnitude is `<= 1`; for larger magnitudes the same *relative*
//! bound holds because `s` shrinks exactly as fast as the magnitude grows
//! (`m - l` term). `R4` (monotone) holds because floor/ceil/round-half-away-
//! from-zero of `value * 2^s` are each monotone in `value` for fixed `s`, and
//! `s` itself is a monotone (non-increasing) function of `value`'s magnitude
//! -- verified empirically in `tests/property.rs`, not yet machine-checked.
//!
//! ## Magnitude ceiling (a spec clarification, not in the original text)
//!
//! `I2` bounds `|num| <= 2^62 - 1` directly, not just precision: a rational
//! value's magnitude is a lower bound on `|num|` for *any* valid
//! denominator (`|num| = |value| * den >= |value|`). So if the exact
//! mathematical result of an op has magnitude `> 2^62 - 1`, no canonical `Q`
//! -- rounded or not -- can represent it, even approximately within `R3`
//! (the error bound is relative to a magnitude the result itself could never
//! reach). The spec's own sizing analysis (§4.4) notes this never happens in
//! the consuming engine (opinion values stay in `[0, 1]`), so this is a
//! theoretical edge only. This implementation **saturates** to
//! `±(2^62 - 1)/1` in that case rather than panicking, documented here and
//! covered by `tests/adversarial.rs`. `Down`/`Up` directedness cannot be
//! honored past the ceiling (there is no representable value on the correct
//! side); `Nearest` saturation is the honest closest answer.

use crate::q::Q;

/// `2^62 - 1`, the `I2` bound on both `|num|` and `den`.
pub const MAX_MAGNITUDE: i64 = (1i64 << 62) - 1;
const MAX_MAGNITUDE_U128: u128 = MAX_MAGNITUDE as u128;

/// Directed rounding mode. `Down`/`Up` bracket the exact value (`R2`);
/// `Nearest` is what all plain arithmetic ops use.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Dir {
    Down,
    Up,
    Nearest,
}

fn gcd_u128(mut a: u128, mut b: u128) -> u128 {
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    a
}

/// Sign-normalize (`den > 0`) and GCD-reduce an exact `num/den` pair.
/// Requires `den != 0`. `0` always canonicalizes to `(0, 1)`.
fn canonicalize_i128(num: i128, den: i128) -> (i128, i128) {
    debug_assert!(den != 0, "canonicalize_i128: den == 0");
    let (num, den) = if den < 0 { (-num, -den) } else { (num, den) };
    if num == 0 {
        return (0, 1);
    }
    let g = gcd_u128(num.unsigned_abs(), den as u128) as i128;
    (num / g, den / g)
}

fn fits_budget(num: i128, den: i128) -> bool {
    num.unsigned_abs() <= MAX_MAGNITUDE_U128 && (den as u128) <= MAX_MAGNITUDE_U128
}

fn bitlen_u128(x: u128) -> u32 {
    u128::BITS - x.leading_zeros()
}

/// Round a coprime, sign-normalized, out-of-budget `num/den` (`den > 0`) to
/// the nearest (or directed) representable `Q`, per `R1`-`R4` and the
/// magnitude-ceiling clarification above.
fn round_to_budget(num: i128, den: i128, dir: Dir) -> Q {
    debug_assert!(den > 0);
    debug_assert!(num != 0, "round_to_budget: 0 is always in-budget");
    debug_assert!(
        !fits_budget(num, den),
        "round_to_budget called on an in-budget value"
    );

    let sign_negative = num < 0;
    let n_mag = num.unsigned_abs();
    let d_mag = den as u128;

    let m = bitlen_u128(n_mag) as i64;
    let l = bitlen_u128(d_mag) as i64;
    // Target: scaled magnitude ~ 2^61 (one bit of headroom under the 2^62-1
    // ceiling to absorb a rounding-up carry).
    let s = (61 - (m - l)).clamp(0, 61) as u32;

    let mut q_mag = n_mag / d_mag;
    let mut r = n_mag % d_mag;
    for _ in 0..s {
        r *= 2;
        if r >= d_mag {
            r -= d_mag;
            q_mag = q_mag * 2 + 1;
        } else {
            q_mag *= 2;
        }
    }
    let exact = r == 0;

    // Direction is expressed on the *value*, not the magnitude: for a
    // negative value, "round down" (toward -inf) means rounding the
    // magnitude *up*.
    let round_down_mag = match dir {
        Dir::Nearest => false, // handled separately below
        Dir::Down => !sign_negative,
        Dir::Up => sign_negative,
    };

    let k_mag: u128 = if exact {
        q_mag
    } else if matches!(dir, Dir::Nearest) {
        // Round half away from zero (in magnitude terms).
        if 2 * r >= d_mag {
            q_mag + 1
        } else {
            q_mag
        }
    } else if round_down_mag {
        q_mag
    } else {
        q_mag + 1
    };

    let (mut k_mag, mut s) = (k_mag, s);
    if k_mag == 0 {
        return Q::zero();
    }
    if k_mag > MAX_MAGNITUDE_U128 {
        // Magnitude ceiling (see module docs): no representable Q, at any
        // shift, can hold a value this large. Only reachable at s == 0 --
        // s > 0 implies q_mag was already <= 2^61-ish by construction, so a
        // rounding-up carry keeps it within the 2^62-1 ceiling. Saturate.
        k_mag = MAX_MAGNITUDE_U128;
        s = 0;
    } else {
        // Reduce k_mag / 2^s by common power-of-two factors.
        let tz = k_mag.trailing_zeros().min(s);
        k_mag >>= tz;
        s -= tz;
    }

    let num_out = if sign_negative {
        -(k_mag as i128)
    } else {
        k_mag as i128
    };
    let den_out = 1i128 << s;
    debug_assert!(fits_budget(num_out, den_out));

    Q::from_canonical_i128(num_out, den_out)
}

/// Canonicalize an exact `num/den` pair and round it into budget if needed.
/// This is the single funnel every arithmetic op uses.
pub(crate) fn from_exact_i128(num: i128, den: i128, dir: Dir) -> Q {
    let (num, den) = canonicalize_i128(num, den);
    if fits_budget(num, den) {
        Q::from_canonical_i128(num, den)
    } else {
        round_to_budget(num, den, dir)
    }
}
