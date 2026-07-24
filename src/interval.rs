use crate::{Dir, Q};

/// A closed interval `[lo, hi]` of rational numbers.
///
/// Both endpoints are `Q` values satisfying invariants I1/I2.
/// All arithmetic widens correctly using directed rounding:
/// the result interval is guaranteed to contain the exact result
/// for all inputs in the operand intervals.
#[derive(Clone, Copy, Debug)]
pub struct Interval {
    lo: Q,
    hi: Q,
}

impl Interval {
    /// Construct from explicit bounds. Panics if `lo > hi`.
    pub fn new(lo: Q, hi: Q) -> Self {
        assert!(lo <= hi, "Interval::new: lo > hi");
        Interval { lo, hi }
    }

    /// A point interval `[v, v]`.
    #[inline]
    pub fn point(v: Q) -> Self {
        Interval { lo: v, hi: v }
    }

    /// The zero interval `[0, 0]`.
    #[inline]
    pub fn zero() -> Self {
        Self::point(Q::zero())
    }

    /// The one interval `[1, 1]`.
    #[inline]
    pub fn one() -> Self {
        Self::point(Q::one())
    }

    /// The unit interval `[0, 1]`.
    #[inline]
    pub fn unit() -> Self {
        Interval {
            lo: Q::zero(),
            hi: Q::one(),
        }
    }

    /// Lower bound.
    #[inline]
    pub fn lo(&self) -> Q {
        self.lo
    }

    /// Upper bound.
    #[inline]
    pub fn hi(&self) -> Q {
        self.hi
    }

    /// Midpoint: `(lo + hi) / 2`, rounded to nearest.
    pub fn midpoint(&self) -> Q {
        let two = Q::from_int(2).unwrap();
        (self.lo + self.hi) / two
    }

    /// Width: `hi - lo`, always non-negative.
    pub fn width(&self) -> Q {
        self.hi - self.lo
    }

    /// Does this interval contain the point `v`?
    #[inline]
    pub fn contains(&self, v: Q) -> bool {
        v >= self.lo && v <= self.hi
    }

    /// Is this a point interval (lo == hi)?
    #[inline]
    pub fn is_point(&self) -> bool {
        self.lo == self.hi
    }

    /// Does this interval overlap with another?
    #[inline]
    pub fn overlaps(&self, other: &Interval) -> bool {
        self.lo <= other.hi && other.lo <= self.hi
    }

    /// Intersection. Returns `None` if disjoint.
    pub fn intersect(&self, other: &Interval) -> Option<Interval> {
        let lo = self.lo.max(other.lo);
        let hi = self.hi.min(other.hi);
        if lo <= hi {
            Some(Interval { lo, hi })
        } else {
            None
        }
    }

    /// Hull (smallest interval containing both).
    pub fn hull(&self, other: &Interval) -> Interval {
        Interval {
            lo: self.lo.min(other.lo),
            hi: self.hi.max(other.hi),
        }
    }

    // ============================================================
    // Arithmetic
    // ============================================================

    /// `[a,b] + [c,d] = [a+c rounded down, b+d rounded up]`
    pub fn add(&self, other: &Interval) -> Interval {
        Interval {
            lo: self.lo.add_dir(other.lo, Dir::Down),
            hi: self.hi.add_dir(other.hi, Dir::Up),
        }
    }

    /// `[a,b] - [c,d] = [a-d rounded down, b-c rounded up]`
    pub fn sub(&self, other: &Interval) -> Interval {
        Interval {
            lo: self.lo.sub_dir(other.hi, Dir::Down),
            hi: self.hi.sub_dir(other.lo, Dir::Up),
        }
    }

    /// Interval multiplication using the four-corners method.
    ///
    /// For `[a,b] * [c,d]`, the result is `[min(ac,ad,bc,bd), max(ac,ad,bc,bd)]`
    /// with appropriate directed rounding.
    pub fn mul(&self, other: &Interval) -> Interval {
        let corners = [
            (self.lo, other.lo),
            (self.lo, other.hi),
            (self.hi, other.lo),
            (self.hi, other.hi),
        ];

        let mut lo = corners[0].0.mul_dir(corners[0].1, Dir::Down);
        let mut hi = corners[0].0.mul_dir(corners[0].1, Dir::Up);

        for &(a, b) in &corners[1..] {
            let low = a.mul_dir(b, Dir::Down);
            let high = a.mul_dir(b, Dir::Up);
            if low < lo {
                lo = low;
            }
            if high > hi {
                hi = high;
            }
        }

        Interval { lo, hi }
    }

    /// Interval division. Panics if `other` contains zero.
    pub fn div(&self, other: &Interval) -> Interval {
        assert!(
            other.lo > Q::zero() || other.hi < Q::zero(),
            "Interval::div: divisor contains zero"
        );

        let corners = [
            (self.lo, other.lo),
            (self.lo, other.hi),
            (self.hi, other.lo),
            (self.hi, other.hi),
        ];

        let mut lo = corners[0].0.div_dir(corners[0].1, Dir::Down);
        let mut hi = corners[0].0.div_dir(corners[0].1, Dir::Up);

        for &(a, b) in &corners[1..] {
            let low = a.div_dir(b, Dir::Down);
            let high = a.div_dir(b, Dir::Up);
            if low < lo {
                lo = low;
            }
            if high > hi {
                hi = high;
            }
        }

        Interval { lo, hi }
    }

    /// Negation: `[-hi, -lo]`.
    #[inline]
    pub fn neg(&self) -> Interval {
        Interval {
            lo: -self.hi,
            hi: -self.lo,
        }
    }

    /// Absolute value interval.
    pub fn abs(&self) -> Interval {
        if self.lo >= Q::zero() {
            *self
        } else if self.hi <= Q::zero() {
            self.neg()
        } else {
            Interval {
                lo: Q::zero(),
                hi: self.lo.abs().max(self.hi.abs()),
            }
        }
    }

    /// Reciprocal: `1 / [lo, hi]`. Panics if interval contains zero.
    pub fn recip(&self) -> Interval {
        assert!(
            self.lo > Q::zero() || self.hi < Q::zero(),
            "Interval::recip: interval contains zero"
        );
        Interval {
            lo: self.hi.recip().min(self.lo.recip()),
            hi: self.hi.recip().max(self.lo.recip()),
        }
    }

    /// Clamp every point in this interval to `[lo, hi]`.
    pub fn clamp(&self, lo: Q, hi: Q) -> Interval {
        Interval {
            lo: self.lo.max(lo),
            hi: self.hi.min(hi),
        }
    }

    // ============================================================
    // Lipschitz error propagation
    // ============================================================

    /// Lipschitz widening: if `f` is `L`-Lipschitz on the domain of `self`,
    /// then `f(x)` for any `x ∈ self` lies within `center ± L · width(self)/2`.
    ///
    /// Returns the interval `[center - L·w/2, center + L·w/2]` rounded outward.
    ///
    /// Use case: when `f(midpoint)` is known but `f` over the full interval
    /// is expensive, and a Lipschitz constant `L` is available.
    pub fn lipschitz_widen(&self, center: Q, lip: Q) -> Interval {
        let half_width = self.width().div_dir(Q::from_int(2).unwrap(), Dir::Up);
        let margin = lip.abs().mul_dir(half_width, Dir::Up);
        Interval {
            lo: center.sub_dir(margin, Dir::Down),
            hi: center.add_dir(margin, Dir::Up),
        }
    }

    /// Lipschitz composition: given `f([a,b]) ⊆ result` and `f` is `L`-Lipschitz,
    /// tighten the output interval to `f(mid) ± L·(b-a)/2` if that's tighter
    /// than the direct interval evaluation.
    ///
    /// `f_mid` is `f(midpoint(self))`, pre-computed by the caller.
    pub fn lipschitz_tighten(&self, direct: Interval, f_mid: Q, lip: Q) -> Interval {
        let lip_interval = self.lipschitz_widen(f_mid, lip);
        match direct.intersect(&lip_interval) {
            Some(tighter) => tighter,
            None => direct,
        }
    }

    /// Affine image: `a * self + b`, with outward rounding.
    ///
    /// For a linear function `f(x) = a·x + b` (which is `|a|`-Lipschitz),
    /// this computes the exact image interval.
    pub fn affine(&self, a: Q, b: Q) -> Interval {
        let scaled = Interval::point(a).mul(self);
        scaled.add(&Interval::point(b))
    }
}

impl std::fmt::Display for Interval {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[{}, {}]", self.lo, self.hi)
    }
}

impl PartialEq for Interval {
    fn eq(&self, other: &Self) -> bool {
        self.lo == other.lo && self.hi == other.hi
    }
}

impl Eq for Interval {}

impl std::ops::Add for Interval {
    type Output = Interval;
    #[inline]
    fn add(self, rhs: Interval) -> Interval {
        Interval::add(&self, &rhs)
    }
}

impl std::ops::Sub for Interval {
    type Output = Interval;
    #[inline]
    fn sub(self, rhs: Interval) -> Interval {
        Interval::sub(&self, &rhs)
    }
}

impl std::ops::Mul for Interval {
    type Output = Interval;
    #[inline]
    fn mul(self, rhs: Interval) -> Interval {
        Interval::mul(&self, &rhs)
    }
}

impl std::ops::Div for Interval {
    type Output = Interval;
    #[inline]
    fn div(self, rhs: Interval) -> Interval {
        Interval::div(&self, &rhs)
    }
}

impl std::ops::Neg for Interval {
    type Output = Interval;
    #[inline]
    fn neg(self) -> Interval {
        Interval::neg(&self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn point_interval() {
        let p = Interval::point(Q::new(1, 2).unwrap());
        assert!(p.is_point());
        assert_eq!(p.width(), Q::zero());
        assert!(p.contains(Q::new(1, 2).unwrap()));
        assert!(!p.contains(Q::new(1, 3).unwrap()));
    }

    #[test]
    fn unit_interval() {
        let u = Interval::unit();
        assert!(u.contains(Q::zero()));
        assert!(u.contains(Q::one()));
        assert!(u.contains(Q::new(1, 2).unwrap()));
        assert!(!u.contains(Q::new(3, 2).unwrap()));
        assert!(!u.contains(Q::new(-1, 2).unwrap()));
    }

    #[test]
    fn add_intervals() {
        let a = Interval::new(Q::new(1, 4).unwrap(), Q::new(1, 2).unwrap());
        let b = Interval::new(Q::new(1, 3).unwrap(), Q::new(2, 3).unwrap());
        let r = a + b;
        // [1/4 + 1/3, 1/2 + 2/3] = [7/12, 7/6]
        assert!(r.lo() <= Q::new(7, 12).unwrap());
        assert!(r.hi() >= Q::new(7, 6).unwrap());
    }

    #[test]
    fn sub_intervals() {
        let a = Interval::new(Q::new(1, 2).unwrap(), Q::one());
        let b = Interval::new(Q::new(1, 4).unwrap(), Q::new(1, 3).unwrap());
        let r = a - b;
        // [1/2 - 1/3, 1 - 1/4] = [1/6, 3/4]
        assert!(r.lo() <= Q::new(1, 6).unwrap());
        assert!(r.hi() >= Q::new(3, 4).unwrap());
    }

    #[test]
    fn mul_intervals() {
        let a = Interval::new(Q::new(2, 1).unwrap(), Q::new(3, 1).unwrap());
        let b = Interval::new(Q::new(4, 1).unwrap(), Q::new(5, 1).unwrap());
        let r = a * b;
        // [2*4, 3*5] = [8, 15]
        assert!(r.lo() <= Q::new(8, 1).unwrap());
        assert!(r.hi() >= Q::new(15, 1).unwrap());
    }

    #[test]
    fn mul_mixed_sign() {
        let a = Interval::new(Q::new(-2, 1).unwrap(), Q::new(3, 1).unwrap());
        let b = Interval::new(Q::new(-1, 1).unwrap(), Q::new(4, 1).unwrap());
        let r = a * b;
        // corners: (-2)(-1)=2, (-2)(4)=-8, (3)(-1)=-3, (3)(4)=12
        // min=-8, max=12
        assert!(r.lo() <= Q::new(-8, 1).unwrap());
        assert!(r.hi() >= Q::new(12, 1).unwrap());
    }

    #[test]
    fn div_positive() {
        let a = Interval::new(Q::new(1, 1).unwrap(), Q::new(4, 1).unwrap());
        let b = Interval::new(Q::new(2, 1).unwrap(), Q::new(8, 1).unwrap());
        let r = a / b;
        // corners: 1/2, 1/8, 4/2=2, 4/8=1/2 → [1/8, 2]
        assert!(r.lo() <= Q::new(1, 8).unwrap());
        assert!(r.hi() >= Q::new(2, 1).unwrap());
    }

    #[test]
    #[should_panic(expected = "divisor contains zero")]
    fn div_contains_zero_panics() {
        let a = Interval::unit();
        let b = Interval::new(Q::new(-1, 1).unwrap(), Q::new(1, 1).unwrap());
        let _ = a / b;
    }

    #[test]
    fn negation() {
        let a = Interval::new(Q::new(1, 4).unwrap(), Q::new(3, 4).unwrap());
        let neg = -a;
        assert_eq!(neg.lo(), Q::new(-3, 4).unwrap());
        assert_eq!(neg.hi(), Q::new(-1, 4).unwrap());
    }

    #[test]
    fn abs_positive() {
        let a = Interval::new(Q::new(1, 4).unwrap(), Q::new(3, 4).unwrap());
        assert_eq!(a.abs(), a);
    }

    #[test]
    fn abs_negative() {
        let a = Interval::new(Q::new(-3, 4).unwrap(), Q::new(-1, 4).unwrap());
        let r = a.abs();
        assert_eq!(r.lo(), Q::new(1, 4).unwrap());
        assert_eq!(r.hi(), Q::new(3, 4).unwrap());
    }

    #[test]
    fn abs_mixed() {
        let a = Interval::new(Q::new(-1, 4).unwrap(), Q::new(3, 4).unwrap());
        let r = a.abs();
        assert_eq!(r.lo(), Q::zero());
        assert_eq!(r.hi(), Q::new(3, 4).unwrap());
    }

    #[test]
    fn hull_and_intersect() {
        let a = Interval::new(Q::new(0, 1).unwrap(), Q::new(3, 4).unwrap());
        let b = Interval::new(Q::new(1, 4).unwrap(), Q::one());
        let h = a.hull(&b);
        assert_eq!(h.lo(), Q::zero());
        assert_eq!(h.hi(), Q::one());

        let i = a.intersect(&b).unwrap();
        assert_eq!(i.lo(), Q::new(1, 4).unwrap());
        assert_eq!(i.hi(), Q::new(3, 4).unwrap());
    }

    #[test]
    fn disjoint_intersect() {
        let a = Interval::new(Q::zero(), Q::new(1, 4).unwrap());
        let b = Interval::new(Q::new(1, 2).unwrap(), Q::one());
        assert!(a.intersect(&b).is_none());
    }

    #[test]
    fn midpoint_width() {
        let a = Interval::new(Q::new(1, 4).unwrap(), Q::new(3, 4).unwrap());
        assert_eq!(a.midpoint(), Q::new(1, 2).unwrap());
        assert_eq!(a.width(), Q::new(1, 2).unwrap());
    }

    #[test]
    fn affine_transform() {
        let x = Interval::new(Q::zero(), Q::one());
        // f(x) = 2x + 1 maps [0,1] to [1,3]
        let two = Q::from_int(2).unwrap();
        let one = Q::one();
        let r = x.affine(two, one);
        assert!(r.lo() <= Q::one());
        assert!(r.hi() >= Q::new(3, 1).unwrap());
    }

    #[test]
    fn lipschitz_widen_test() {
        let x = Interval::new(Q::new(1, 4).unwrap(), Q::new(3, 4).unwrap());
        let center = Q::new(1, 2).unwrap();
        let lip = Q::new(2, 1).unwrap();
        // width = 1/2, half_width = 1/4, margin = 2 * 1/4 = 1/2
        // result = [1/2 - 1/2, 1/2 + 1/2] = [0, 1]
        let r = x.lipschitz_widen(center, lip);
        assert!(r.lo() <= Q::zero());
        assert!(r.hi() >= Q::one());
    }

    #[test]
    fn lipschitz_tighten_test() {
        let x = Interval::new(Q::zero(), Q::one());
        let direct = Interval::new(Q::new(-1, 1).unwrap(), Q::new(3, 1).unwrap());
        let f_mid = Q::new(1, 2).unwrap();
        let lip = Q::one();
        // Lipschitz gives [1/2 - 1*1/2, 1/2 + 1*1/2] = [0, 1]
        // intersect([-1,3], [0,1]) = [0, 1]
        let r = x.lipschitz_tighten(direct, f_mid, lip);
        assert!(r.lo() >= Q::zero() || r.lo() == Q::zero());
        assert!(r.hi() <= Q::one() || r.hi() == Q::one());
    }

    #[test]
    fn display() {
        let a = Interval::new(Q::new(1, 3).unwrap(), Q::new(2, 3).unwrap());
        assert_eq!(format!("{a}"), "[1/3, 2/3]");
    }

    #[test]
    fn recip_interval() {
        let a = Interval::new(Q::new(2, 1).unwrap(), Q::new(4, 1).unwrap());
        let r = a.recip();
        assert_eq!(r.lo(), Q::new(1, 4).unwrap());
        assert_eq!(r.hi(), Q::new(1, 2).unwrap());
    }

    #[test]
    #[should_panic(expected = "interval contains zero")]
    fn recip_contains_zero_panics() {
        let a = Interval::new(Q::new(-1, 1).unwrap(), Q::one());
        let _ = a.recip();
    }
}
