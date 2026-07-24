// M6: Interval Rational Arithmetic (QI = [lo: Q, hi: Q])
// Verified interval type for uncertainty propagation

use crate::q::Q;
use std::fmt;

/// Interval rational number: [lo, hi] where lo <= hi
/// Represents the set of all rationals q where lo <= q <= hi
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct QI {
    pub lo: Q,
    pub hi: Q,
}

impl QI {
    /// Create a point interval [q, q]
    pub fn point(q: Q) -> Self {
        QI { lo: q, hi: q }
    }

    /// Create an interval [lo, hi] with validation
    /// Returns None if lo > hi (invalid interval)
    pub fn interval(lo: Q, hi: Q) -> Option<Self> {
        if lo <= hi {
            Some(QI { lo, hi })
        } else {
            None
        }
    }

    /// Width of the interval: hi - lo
    pub fn width(self) -> Q {
        self.hi.sub(self.lo)
    }

    /// Midpoint of the interval: (lo + hi) / 2
    pub fn midpoint(self) -> Q {
        let sum = self.lo.add(self.hi);
        Q::from_int(2).and_then(|two| sum.div(two)).unwrap_or(sum)
    }

    /// Check if interval contains a single point
    pub fn is_point(self) -> bool {
        self.lo == self.hi
    }

    /// Check if interval contains zero
    pub fn contains_zero(self) -> bool {
        self.lo <= Q::zero() && Q::zero() <= self.hi
    }

    /// Add two intervals: [a.lo + b.lo, a.hi + b.hi]
    /// M6.V7: Addition preserves interval containment
    #[allow(clippy::should_implement_trait)]
    pub fn add(self, other: QI) -> QI {
        QI {
            lo: self.lo.add(other.lo),
            hi: self.hi.add(other.hi),
        }
    }

    /// Subtract two intervals: [a.lo - b.hi, a.hi - b.lo]
    #[allow(clippy::should_implement_trait)]
    pub fn sub(self, other: QI) -> QI {
        QI {
            lo: self.lo.sub(other.hi),
            hi: self.hi.sub(other.lo),
        }
    }

    /// Multiply two intervals (handles signs correctly)
    /// M6.V7: Multiplication preserves interval containment (for positive intervals)
    #[allow(clippy::should_implement_trait)]
    pub fn mul(self, other: QI) -> QI {
        // Compute all four corner products
        let ll = self.lo.mul(other.lo);
        let lh = self.lo.mul(other.hi);
        let hl = self.hi.mul(other.lo);
        let hh = self.hi.mul(other.hi);

        // Find min and max among all products
        let lo = ll.min(lh).min(hl).min(hh);
        let hi = ll.max(lh).max(hl).max(hh);

        QI { lo, hi }
    }

    /// Reciprocal of interval
    /// Returns None if interval contains zero (undefined)
    /// M6: Requires 0 ∉ [lo, hi]
    pub fn recip(self) -> Option<QI> {
        if self.contains_zero() {
            return None;
        }

        // For positive intervals [a, b] where a, b > 0: recip is [1/b, 1/a]
        // For negative intervals [a, b] where a, b < 0: recip is [1/b, 1/a] (both endpoints flip)

        let lo_recip = self.hi.recip()?;
        let hi_recip = self.lo.recip()?;

        QI::interval(lo_recip, hi_recip)
    }

    /// Divide two intervals
    #[allow(clippy::should_implement_trait)]
    pub fn div(self, other: QI) -> Option<QI> {
        other.recip().map(|recip| self.mul(recip))
    }

    /// Intersect two intervals: [max(lo1, lo2), min(hi1, hi2)]
    pub fn intersect(self, other: QI) -> Option<QI> {
        let lo = self.lo.max(other.lo);
        let hi = self.hi.min(other.hi);
        QI::interval(lo, hi)
    }

    /// Union of two intervals: [min(lo1, lo2), max(hi1, hi2)]
    pub fn union(self, other: QI) -> QI {
        QI {
            lo: self.lo.min(other.lo),
            hi: self.hi.max(other.hi),
        }
    }

    /// Check if interval contains another interval (monotonicity)
    /// M6.V8: Interval monotonicity
    pub fn contains_interval(self, other: QI) -> bool {
        self.lo <= other.lo && other.hi <= self.hi
    }

    /// Lipschitz bound for addition: perturbation in operands propagates linearly
    /// |add(x + dx, y + dy) - add(x, y)| <= |dx| + |dy|
    /// Returns the perturbed result
    pub fn add_perturbed(self, x_perturb: QI, other: QI, y_perturb: QI) -> QI {
        // Result = [x_lo + dx_lo + y_lo + dy_lo, x_hi + dx_hi + y_hi + dy_hi]
        self.add(x_perturb).add(other).add(y_perturb)
    }

    /// Absolute value of interval
    pub fn abs(self) -> QI {
        if self.lo >= Q::zero() {
            self // [a, b] with a >= 0
        } else if self.hi <= Q::zero() {
            QI {
                lo: self.hi.abs(),
                hi: self.lo.abs(),
            } // [-b, -a] for [a, b] with b <= 0
        } else {
            // [-a, a] for [a, b] with a < 0 < b
            QI {
                lo: Q::zero(),
                hi: self.lo.abs().max(self.hi.abs()),
            }
        }
    }

    /// Negation of interval: [-hi, -lo]
    #[allow(clippy::should_implement_trait)]
    pub fn neg(self) -> QI {
        QI {
            lo: self.hi.neg(),
            hi: self.lo.neg(),
        }
    }
}

impl fmt::Display for QI {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[{}, {}]", self.lo, self.hi)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_point_interval() {
        let q = Q::one();
        let qi = QI::point(q);
        assert_eq!(qi.lo, q);
        assert_eq!(qi.hi, q);
        assert!(qi.is_point());
    }

    #[test]
    fn test_interval_validation() {
        let lo = Q::zero();
        let hi = Q::one();
        let qi = QI::interval(lo, hi);
        assert!(qi.is_some());

        let invalid = QI::interval(hi, lo);
        assert!(invalid.is_none());
    }

    #[test]
    fn test_contains_zero() {
        let qi1 = QI::interval(Q::from_int(-1).unwrap(), Q::one()).unwrap();
        assert!(qi1.contains_zero());

        let qi2 = QI::interval(Q::one(), Q::from_int(2).unwrap()).unwrap();
        assert!(!qi2.contains_zero());
    }

    #[test]
    fn test_interval_add() {
        let qi1 = QI::interval(Q::zero(), Q::one()).unwrap();
        let qi2 = QI::interval(Q::zero(), Q::one()).unwrap();
        let result = qi1.add(qi2);
        assert_eq!(result.lo, Q::zero());
        // Result should be [0, 2]
    }

    #[test]
    fn test_interval_width() {
        let qi = QI::interval(Q::zero(), Q::one()).unwrap();
        assert_eq!(qi.width(), Q::one());
    }

    #[test]
    fn test_negation() {
        let qi = QI::interval(Q::from_int(-1).unwrap(), Q::one()).unwrap();
        let neg_qi = qi.neg();
        assert_eq!(neg_qi.lo, Q::from_int(-1).unwrap());
        assert_eq!(neg_qi.hi, Q::one());
    }
}
