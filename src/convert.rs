// Boundary conversions: from_decimal, from_f64_dir (via bit decomposition), to_f64.
// from_f64_dir uses integer bit-decomposition of f64 — no float reasoning needed in Verus.
// to_f64 is marked external_body (display/DTO only).

use crate::q::{Q, Dir, BOUND};
use crate::gcd::gcd_exec;

/// Exact decimal ingestion: `from_decimal(85, 2)` → 85/100 → 17/20 = 0.85.
/// Returns None if dec_places ≥ 20 (10^20 > i128) or if mantissa exceeds BOUND after reduction.
pub fn from_decimal(mantissa: i64, dec_places: u8) -> Option<Q> {
    if dec_places >= 20 {
        return None;
    }
    let scale = 10i128.pow(dec_places as u32);
    let n = mantissa as i128;
    let d = scale;
    if d == 0 { return None; }
    // Reduce and check bounds.
    let abs_n = if n < 0 { -n } else { n } as u64;
    let g = gcd_exec(abs_n, d as u64) as i128;
    let num_r = n / g;
    let den_r = d / g;
    if num_r < -(BOUND as i128) || num_r > BOUND as i128 || den_r > BOUND as i128 {
        return None;
    }
    Some(Q { num: num_r as i64, den: den_r as i64 })
}

/// Convert f64 to Q by exact bit decomposition (no float arithmetic).
///
/// An f64 is `(-1)^sign * mantissa * 2^exp` with a 52-bit explicit fraction.
/// This is always a rational — we convert it exactly, then round to budget if needed.
/// Returns None on NaN, ±inf, or |v| > 2^61.
pub fn from_f64_dir(v: f64, dir: Dir) -> Option<Q> {
    let bits = v.to_bits();
    let sign = (bits >> 63) & 1;
    let exp_biased = ((bits >> 52) & 0x7ff) as i32;
    let mantissa = bits & 0x000f_ffff_ffff_ffff;

    // NaN or inf
    if exp_biased == 0x7ff {
        return None;
    }

    if exp_biased == 0 && mantissa == 0 {
        // ±0
        return Some(Q::zero());
    }

    let (m, e): (i128, i32) = if exp_biased == 0 {
        // Subnormal: value = mantissa * 2^(1 - 1023 - 52) = mantissa * 2^(-1074)
        (mantissa as i128, -1074)
    } else {
        // Normal: value = (2^52 + mantissa) * 2^(exp_biased - 1023 - 52)
        ((mantissa as i128) | (1i128 << 52), exp_biased - 1023 - 52)
    };

    let m_signed = if sign == 1 { -m } else { m };

    // Value = m_signed * 2^e.
    // Range check: |v| > 2^61 is rejected.
    if e >= 9 {
        // m has at most 53 bits, so |value| = |m| * 2^e ≥ 2^(e) (for nonzero m).
        // e >= 9 means |value| could be > 2^61; check precisely.
        if e >= 62 {
            return None; // definitely over limit
        }
        // m_signed * 2^e: m_signed fits i128, shift is small, check against 2^61
        let limit: i128 = 1i128 << 61;
        let abs_val = if m_signed < 0 { -m_signed } else { m_signed };
        if abs_val > (limit >> e) {
            return None;
        }
    }

    if e >= 0 {
        // Positive exponent: exact integer value = m_signed * 2^e.
        let val = m_signed.checked_shl(e as u32)?;
        if val.abs() > BOUND as i128 {
            return None;
        }
        Some(Q { num: val as i64, den: 1 })
    } else {
        // Negative exponent: value = m_signed / 2^(-e).
        let neg_e = (-e) as u32;
        if neg_e >= 127 {
            // Extremely small: rounds to 0.
            return Some(match dir {
                Dir::Up if m_signed > 0 => Q { num: 1, den: BOUND },
                Dir::Down if m_signed < 0 => Q { num: -1, den: BOUND },
                _ => Q::zero(),
            });
        }
        let num = m_signed;
        let den = 1i128 << neg_e;
        // Reduce and round to budget.
        let abs_n = if num < 0 { -num } else { num } as u64;
        let g = gcd_exec(abs_n, den as u64) as i128;
        let num_r = num / g;
        let den_r = den / g;
        if num_r >= -(BOUND as i128) && num_r <= BOUND as i128 && den_r <= BOUND as i128 {
            Some(Q { num: num_r as i64, den: den_r as i64 })
        } else {
            Some(crate::round::round_to_budget(num_r, den_r, dir))
        }
    }
}

/// Convert Q to f64 for display/DTO purposes ONLY.
/// This is the one trusted boundary: not verified, covered by differential tests.
/// NEVER feed the result back into Q arithmetic.
#[inline]
pub fn to_f64(q: Q) -> f64 {
    q.num as f64 / q.den as f64
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn decimal_ingestion() {
        let q = from_decimal(85, 2).unwrap();
        assert_eq!(q.num, 17); assert_eq!(q.den, 20); // 0.85 = 17/20

        let q2 = from_decimal(1, 4).unwrap();
        assert_eq!(q2.num, 1); assert_eq!(q2.den, 10000); // 0.0001

        assert_eq!(from_decimal(0, 3).unwrap().num, 0);
    }

    #[test]
    fn from_f64_exact_integers() {
        let q = from_f64_dir(1.0, Dir::Nearest).unwrap();
        assert_eq!(q.num, 1); assert_eq!(q.den, 1);

        let q = from_f64_dir(-3.0, Dir::Nearest).unwrap();
        assert_eq!(q.num, -3); assert_eq!(q.den, 1);

        let q = from_f64_dir(0.0, Dir::Nearest).unwrap();
        assert_eq!(q.num, 0);
    }

    #[test]
    fn from_f64_halves() {
        let q = from_f64_dir(0.5, Dir::Nearest).unwrap();
        assert_eq!(q.num, 1); assert_eq!(q.den, 2);

        let q = from_f64_dir(0.25, Dir::Nearest).unwrap();
        assert_eq!(q.num, 1); assert_eq!(q.den, 4);

        let q = from_f64_dir(0.75, Dir::Nearest).unwrap();
        assert_eq!(q.num, 3); assert_eq!(q.den, 4);
    }

    #[test]
    fn from_f64_nan_inf_rejected() {
        assert!(from_f64_dir(f64::NAN, Dir::Nearest).is_none());
        assert!(from_f64_dir(f64::INFINITY, Dir::Nearest).is_none());
        assert!(from_f64_dir(f64::NEG_INFINITY, Dir::Nearest).is_none());
    }

    #[test]
    fn to_f64_roundtrip_display() {
        let q = Q::new(1, 3).unwrap();
        let f = to_f64(q);
        assert!((f - 0.333333333).abs() < 1e-8);
    }
}
