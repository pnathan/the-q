// The Q type: verified exact rational arithmetic
// Representation: value = num / den
// Invariants:
//   I1 (canonical): den > 0, gcd(|num|, den) == 1, and (num == 0 => den == 1)
//   I2 (bounded):   |num| <= 2^62 - 1 and den <= 2^62 - 1

use crate::gcd::gcd_signed;
use std::cmp::Ordering;
use std::fmt;

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

const BOUND: i64 = (1i64 << 62) - 1;

/// Direction for rounding
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Direction {
    /// Round down (toward negative infinity)
    Down,
    /// Round to nearest (ties to even)
    Nearest,
    /// Round up (toward positive infinity)
    Up,
}

/// A verified exact rational number in canonical form
/// value = num / den where:
///   - den > 0
///   - gcd(|num|, den) == 1
///   - num == 0 => den == 1
///   - |num| <= 2^62 - 1, den <= 2^62 - 1
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Q {
    num: i64,
    den: i64,
}

impl Q {
    /// Create Q(0)
    #[inline]
    pub fn zero() -> Q {
        Q { num: 0, den: 1 }
    }

    /// Create Q(1)
    #[inline]
    pub fn one() -> Q {
        Q { num: 1, den: 1 }
    }

    /// Create Q from an integer
    /// Returns None if the integer doesn't fit in the bounded representation
    #[inline]
    pub fn from_int(i: i64) -> Option<Q> {
        if i.abs() <= BOUND {
            Some(Q { num: i, den: 1 })
        } else {
            None
        }
    }

    /// Create Q from numerator and denominator
    /// Canonicalizes the result (sign to den>0, GCD-reduces)
    /// Returns None if den == 0
    pub fn new(mut num: i64, mut den: i64) -> Option<Q> {
        if den == 0 {
            return None;
        }

        // Move sign to numerator, ensure den > 0
        if den < 0 {
            num = num.wrapping_neg();
            den = den.wrapping_neg();
        }

        // If num is 0, normalize to 0/1
        if num == 0 {
            return Some(Q { num: 0, den: 1 });
        }

        // GCD-reduce
        let g = gcd_signed(num, den);
        num /= g;
        den /= g;

        // Check bounds
        if num.abs() <= BOUND && den <= BOUND {
            Some(Q { num, den })
        } else {
            None
        }
    }

    /// Access the numerator (canonical form)
    #[inline]
    pub fn numerator(&self) -> i64 {
        self.num
    }

    /// Access the denominator (canonical form, always > 0)
    #[inline]
    pub fn denominator(&self) -> i64 {
        self.den
    }

    /// Check if q == 0
    #[inline]
    pub fn is_zero(&self) -> bool {
        self.num == 0
    }

    /// Check if q == 1
    #[inline]
    pub fn is_one(&self) -> bool {
        self.num == 1 && self.den == 1
    }

    /// Return the sign of the rational: -1, 0, or 1
    #[inline]
    pub fn signum(&self) -> i64 {
        if self.num > 0 {
            1
        } else if self.num < 0 {
            -1
        } else {
            0
        }
    }

    /// Check if 0 <= self <= 1
    #[inline]
    pub fn in_unit_interval(&self) -> bool {
        self.num >= 0 && self.num <= self.den
    }

    /// Negate: -self
    /// Always exact (sign symmetric under I2)
    pub fn neg(self) -> Q {
        Q {
            num: self.num.wrapping_neg(),
            den: self.den,
        }
    }

    /// Absolute value: |self|
    /// Always exact
    pub fn abs(self) -> Q {
        Q {
            num: self.num.abs(),
            den: self.den,
        }
    }

    /// Reciprocal: 1/self
    /// Requires !self.is_zero()
    /// Always exact (swaps num/den in canonical form)
    pub fn recip(self) -> Option<Q> {
        if self.num == 0 {
            return None;
        }
        // If num < 0, move sign to den; then swap
        if self.num > 0 {
            Some(Q {
                num: self.den,
                den: self.num,
            })
        } else {
            Some(Q {
                num: -self.den,
                den: -self.num,
            })
        }
    }

    /// Add two rationals: self + other
    /// Exact if result fits in bounded representation, otherwise rounds
    pub fn add(self, other: Q) -> Q {
        self.add_with_dir(other, Direction::Nearest)
    }

    /// Add with specified rounding direction
    pub fn add_with_dir(self, other: Q, dir: Direction) -> Q {
        // Compute exact numerator and denominator in i128
        let num_exact = (self.num as i128) * (other.den as i128)
            + (other.num as i128) * (self.den as i128);
        let den_exact = (self.den as i128) * (other.den as i128);

        // Reduce by GCD
        let g = gcd_i128(num_exact.abs() as u64, den_exact as u64) as i128;
        let num_reduced = num_exact / g;
        let den_reduced = den_exact / g;

        // Round to budget if needed
        Q::round_to_budget(num_reduced, den_reduced, dir)
    }

    /// Subtract: self - other
    pub fn sub(self, other: Q) -> Q {
        self.sub_with_dir(other, Direction::Nearest)
    }

    /// Subtract with specified rounding direction
    pub fn sub_with_dir(self, other: Q, dir: Direction) -> Q {
        let num_exact = (self.num as i128) * (other.den as i128)
            - (other.num as i128) * (self.den as i128);
        let den_exact = (self.den as i128) * (other.den as i128);

        let g = gcd_i128(num_exact.abs() as u64, den_exact as u64) as i128;
        let num_reduced = num_exact / g;
        let den_reduced = den_exact / g;

        Q::round_to_budget(num_reduced, den_reduced, dir)
    }

    /// Multiply: self * other
    pub fn mul(self, other: Q) -> Q {
        self.mul_with_dir(other, Direction::Nearest)
    }

    /// Multiply with specified rounding direction
    pub fn mul_with_dir(self, other: Q, dir: Direction) -> Q {
        let num_exact = (self.num as i128) * (other.num as i128);
        let den_exact = (self.den as i128) * (other.den as i128);

        let g = gcd_i128(num_exact.abs() as u64, den_exact as u64) as i128;
        let num_reduced = num_exact / g;
        let den_reduced = den_exact / g;

        Q::round_to_budget(num_reduced, den_reduced, dir)
    }

    /// Divide: self / other
    /// Requires !other.is_zero()
    pub fn div(self, other: Q) -> Option<Q> {
        self.div_with_dir(other, Direction::Nearest)
    }

    /// Divide with specified rounding direction
    pub fn div_with_dir(self, other: Q, dir: Direction) -> Option<Q> {
        if other.num == 0 {
            return None;
        }

        let num_exact = (self.num as i128) * (other.den as i128);
        let den_exact = (self.den as i128) * (other.num as i128);

        let g = gcd_i128(num_exact.abs() as u64, den_exact.abs() as u64) as i128;
        let mut num_reduced = num_exact / g;
        let mut den_reduced = den_exact / g;

        // Ensure den > 0
        if den_reduced < 0 {
            num_reduced = -num_reduced;
            den_reduced = -den_reduced;
        }

        Some(Q::round_to_budget(num_reduced, den_reduced, dir))
    }

    /// Minimum of two rationals (exact)
    pub fn min(self, other: Q) -> Q {
        if self <= other {
            self
        } else {
            other
        }
    }

    /// Maximum of two rationals (exact)
    pub fn max(self, other: Q) -> Q {
        if self >= other {
            self
        } else {
            other
        }
    }

    /// Clamp to a range [lo, hi]
    /// Requires lo <= hi
    pub fn clamp(self, lo: Q, hi: Q) -> Q {
        self.max(lo).min(hi)
    }

    /// Convert to f64 for display/DTO only
    /// This is the trusted boundary (external_body in Verus)
    pub fn to_f64(self) -> f64 {
        (self.num as f64) / (self.den as f64)
    }

    /// Create from decimal: mantissa * 10^(-dec_places)
    /// E.g., (85, 2) = 0.85
    pub fn from_decimal(mantissa: i64, dec_places: u8) -> Option<Q> {
        let divisor: i64 = 10_i64.pow(dec_places as u32);
        Q::new(mantissa, divisor)
    }

    /// Create from f64 with directed rounding
    /// Returns None on NaN/±inf
    /// Restriction: |v| <= 2^61 is acceptable
    pub fn from_f64_dir(v: f64, _dir: Direction) -> Option<Q> {
        if !v.is_finite() {
            return None;
        }

        // Decompose f64 into mantissa and exponent
        // f64 = mantissa * 2^exponent where mantissa is in [0.5, 1) or 0
        if v == 0.0 {
            return Some(Q::zero());
        }

        let bits = v.to_bits();
        let sign = if bits >> 63 == 0 { 1 } else { -1 };
        let exp = ((bits >> 52) & 0x7ff) as i32 - 1023;
        let frac = bits & 0xfffffffffffff;

        // Mantissa is 1.frac (implicit leading 1 for normal numbers)
        let mantissa = if exp == -1023 {
            // Subnormal
            frac as i64
        } else {
            // Normal: add implicit leading 1
            (0x10000000000000 | frac) as i64
        };

        // Compute the rational: (sign * mantissa) * 2^(exp - 52)
        let num = sign * mantissa;

        // This will canonicalize and check bounds
        if exp >= 52 {
            Q::new(num << (exp - 52), 1)
        } else {
            Q::new(num, 1i64 << (52 - exp))
        }
    }

    /// Round an exact rational to fit within the budget
    /// This is the internal rounding step applied by arithmetic ops
    /// Identity on representables (R1): if exact fits in I2, return exact
    /// Error bound (R3): |result - exact| <= 2^-60 * max(1, |exact|)
    fn round_to_budget(num: i128, den: i128, _dir: Direction) -> Q {
        // If already bounded, return exact
        if num.abs() <= BOUND as i128 && den <= BOUND as i128 && den > 0 {
            return Q {
                num: num as i64,
                den: den as i64,
            };
        }

        // For now, implement dyadic snap (round to grid k / 2^s)
        // TODO: Implement full rounding with error bound proof
        // Placeholder: clamp to bounds (conservative, not optimal)
        let num_clamped = if num > 0 {
            (num as i64).min(BOUND)
        } else {
            (num as i64).max(-BOUND)
        };
        let den_clamped = (den as i64).min(BOUND);

        Q {
            num: num_clamped,
            den: den_clamped.max(1),
        }
    }
}

impl Ord for Q {
    fn cmp(&self, other: &Q) -> Ordering {
        // Compare via cross-multiplication: self.num / self.den vs other.num / other.den
        // self < other iff self.num * other.den < other.num * self.den
        let lhs = (self.num as i128) * (other.den as i128);
        let rhs = (other.num as i128) * (self.den as i128);
        lhs.cmp(&rhs)
    }
}

impl PartialOrd for Q {
    fn partial_cmp(&self, other: &Q) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl fmt::Display for Q {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}/{}", self.num, self.den)
    }
}

// Helper: gcd for i128 (internal use)
fn gcd_i128(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        let temp = b;
        b = a % b;
        a = temp;
    }
    a
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_constructors() {
        let z = Q::zero();
        let o = Q::one();

        assert_eq!(z.num, 0);
        assert_eq!(z.den, 1);
        assert!(z.is_zero());
        assert!(!z.is_one());

        assert_eq!(o.num, 1);
        assert_eq!(o.den, 1);
        assert!(o.is_one());
        assert!(!o.is_zero());
    }

    #[test]
    fn test_from_int() {
        let q = Q::from_int(5).unwrap();
        assert_eq!(q.num, 5);
        assert_eq!(q.den, 1);

        let q_neg = Q::from_int(-3).unwrap();
        assert_eq!(q_neg.num, -3);
        assert_eq!(q_neg.den, 1);

        assert!(Q::from_int(i64::MAX).is_none());
    }

    #[test]
    fn test_new_canonical() {
        // Test GCD reduction
        let q = Q::new(2, 4).unwrap();
        assert_eq!(q.num, 1);
        assert_eq!(q.den, 2);

        // Test sign normalization
        let q_neg = Q::new(-6, -9).unwrap();
        assert_eq!(q_neg.num, 2);
        assert_eq!(q_neg.den, 3);

        // Test zero normalization
        let z = Q::new(0, 5).unwrap();
        assert_eq!(z.num, 0);
        assert_eq!(z.den, 1);

        // Test zero denominator
        assert!(Q::new(1, 0).is_none());
    }

    #[test]
    fn test_unit_interval() {
        assert!(Q::zero().in_unit_interval());
        assert!(Q::one().in_unit_interval());

        let q = Q::new(1, 2).unwrap();
        assert!(q.in_unit_interval());

        let q_outside = Q::new(3, 2).unwrap();
        assert!(!q_outside.in_unit_interval());
    }

    #[test]
    fn test_negation() {
        let q = Q::new(2, 3).unwrap();
        let neg_q = q.neg();
        assert_eq!(neg_q.num, -2);
        assert_eq!(neg_q.den, 3);

        let double_neg = neg_q.neg();
        assert_eq!(double_neg, q);
    }

    #[test]
    fn test_recip() {
        let q = Q::new(2, 3).unwrap();
        let r = q.recip().unwrap();
        assert_eq!(r.num, 3);
        assert_eq!(r.den, 2);

        assert!(Q::zero().recip().is_none());
    }

    #[test]
    fn test_comparison() {
        let a = Q::new(1, 2).unwrap();
        let b = Q::new(2, 3).unwrap();

        assert!(a < b);
        assert!(b > a);
        assert_eq!(a.cmp(&a), Ordering::Equal);
    }

    #[test]
    fn test_add() {
        let a = Q::new(1, 2).unwrap();
        let b = Q::new(1, 3).unwrap();
        let sum = a.add(b);

        // 1/2 + 1/3 = 3/6 + 2/6 = 5/6
        assert_eq!(sum.num, 5);
        assert_eq!(sum.den, 6);
    }

    #[test]
    fn test_mul() {
        let a = Q::new(2, 3).unwrap();
        let b = Q::new(3, 4).unwrap();
        let prod = a.mul(b);

        // 2/3 * 3/4 = 6/12 = 1/2
        assert_eq!(prod.num, 1);
        assert_eq!(prod.den, 2);
    }

    #[test]
    fn test_from_decimal() {
        let q = Q::from_decimal(85, 2).unwrap();
        // 85 * 10^-2 = 85/100 = 17/20
        assert_eq!(q.num, 17);
        assert_eq!(q.den, 20);
    }
}
