//! The f64 boundary (spec §5): exactly one trusted function, `to_f64`.
//!
//! `from_f64_dir` is implemented via exact bit decomposition of the IEEE-754
//! representation (every finite `f64` is exactly `+/-mantissa * 2^exp` for
//! integer `mantissa`, `exp`), so it involves **no untrusted float
//! reasoning** at all -- it is plain, exactly-representable integer
//! arithmetic, same as the rest of the crate. Per the spec this means it is
//! not part of the trusted boundary; see `TRUSTED.md`.

use crate::q::Q;
use crate::rounding::from_exact_i128;

pub use crate::rounding::Dir;

/// Decompose a finite, nonzero `f64` into `mantissa * 2^exp` (exact, no
/// rounding): `mantissa` is the 53-bit significand (implicit leading 1
/// folded in for normals), `exp` its binary exponent.
fn decompose(v: f64) -> (i128, i64) {
    let bits = v.to_bits();
    let sign_negative = bits >> 63 == 1;
    let biased_exp = ((bits >> 52) & 0x7FF) as i64;
    let frac = bits & 0x000F_FFFF_FFFF_FFFF;
    let (mantissa, exp) = if biased_exp == 0 {
        // Subnormal: value = frac * 2^(1 - 1023 - 52).
        (frac, 1 - 1023 - 52)
    } else {
        // Normal: value = (2^52 + frac) * 2^(biased_exp - 1023 - 52).
        ((1u64 << 52) | frac, biased_exp - 1023 - 52)
    };
    let mantissa = mantissa as i128;
    (if sign_negative { -mantissa } else { mantissa }, exp)
}

/// Directed conversion from `f64`. `None` on NaN/+-inf, on a magnitude too
/// extreme for the exact `2^exp` shift to fit `i128`, or -- per the spec's
/// documented `|v| <= 2^61` allowance -- on a magnitude that exceeds what
/// `Q` can represent (`I2`'s `2^62 - 1` ceiling). That last case is
/// deliberately a hard rejection, not the `rounding` module's
/// magnitude-ceiling saturation: `from_f64_dir` is the primary decimal/f64
/// ingestion path (spec §5), and silently saturating an out-of-range input
/// to a value that can be many orders of magnitude off (and so violates
/// R3, not just "surprising") is worse than rejecting it outright. Compare
/// `rounding::round_to_budget`'s saturation, which only ever triggers on
/// an *arithmetic op's* exact result -- there, by construction, both
/// operands (and so typically the result, barring pathological inputs)
/// already came from valid, in-range `Q` values.
///
/// Otherwise the exact value is computed with zero float rounding and
/// handed to the same [`from_exact_i128`] every arithmetic op uses, so it
/// inherits R1-R4.
pub fn from_f64_dir(v: f64, dir: Dir) -> Option<Q> {
    if !v.is_finite() {
        return None;
    }
    if v == 0.0 {
        return Some(Q::zero());
    }
    let (mantissa, exp) = decompose(v);
    if mantissa == 0 {
        return Some(Q::zero());
    }
    let (num, den): (i128, i128) = if exp >= 0 {
        let shift = exp as u32;
        let num = mantissa.checked_shl(shift)?;
        if num.unsigned_abs() > crate::rounding::MAX_MAGNITUDE as u128 {
            return None;
        }
        (num, 1)
    } else {
        let shift = (-exp) as u32;
        if shift > 125 {
            return None;
        }
        // mantissa's magnitude is always <= 2^53 - 1 < MAX_MAGNITUDE, so
        // this branch (den > 1) never needs the magnitude check above.
        (mantissa, 1i128 << shift)
    };
    Some(from_exact_i128(num, den, dir))
}

/// Display/DTO boundary only. **Trusted** (`external_body` in Verus terms):
/// proving IEEE-754 division rounding is out of scope for this crate.
/// Covered by differential tests against the exact value instead (see
/// `TRUSTED.md` and `tests/differential.rs`). Never feed the result back
/// into `Q` arithmetic -- use `from_f64_dir` for that direction.
pub fn to_f64(q: Q) -> f64 {
    q.numerator() as f64 / q.denominator() as f64
}
