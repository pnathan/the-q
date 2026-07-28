// Q — bounded rational with verified invariants.
// I1: den > 0, gcd(|num|, den) == 1, (num == 0 => den == 1)
// I2: |num| <= BOUND, den <= BOUND   where BOUND = 2^62 - 1

use vstd::prelude::*;
use crate::gcd::gcd_exec;
use crate::round::round_to_budget;

pub const BOUND: i64 = (1i64 << 62) - 1; // 2^62 - 1

/// Rounding direction for budget-overflow and `from_f64_dir`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Dir {
    Down,
    Up,
    Nearest,
}

/// A rational number num/den in canonical, bounded form.
#[derive(Clone, Copy)]
pub struct Q {
    pub(crate) num: i64,
    pub(crate) den: i64,
}

// ─── Ghost model (spec functions only, inside verus!) ────────────────────────

verus! {

/// Type invariant predicate: I1 ∧ I2.
pub open spec fn wf(q: Q) -> bool {
    &&& (q.den > 0)
    &&& (q.num == 0 ==> q.den == 1)
    &&& (q.num != 0 ==>
        spec_gcd(
            (if q.num >= 0 { q.num as u64 } else { (-q.num) as u64 }),
            q.den as u64,
        ) == 1)
    &&& (-(BOUND as int) <= q.num as int)
    &&& (q.num as int <= BOUND as int)
    &&& (1 <= q.den as int)
    &&& (q.den as int <= BOUND as int)
}

/// Recursive Euclidean GCD, spec only (ghost).
pub open spec fn spec_gcd(a: u64, b: u64) -> u64
    decreases b,
{
    if b == 0 { if a == 0 { 1u64 } else { a } } else { spec_gcd(b, a % b) }
}

/// Cross-multiplication equality (division-free, no ghost int overflow).
pub open spec fn q_eq_val(a: Q, b: Q) -> bool {
    (a.num as int) * (b.den as int) == (b.num as int) * (a.den as int)
}

/// Cross-multiplication less-than-or-equal.
pub open spec fn q_le_val(a: Q, b: Q) -> bool {
    (a.num as int) * (b.den as int) <= (b.num as int) * (a.den as int)
}

/// Cross-multiplication strict less-than.
pub open spec fn q_lt_val(a: Q, b: Q) -> bool {
    (a.num as int) * (b.den as int) < (b.num as int) * (a.den as int)
}

} // verus! (spec block)

// ─── Exec impl (outside verus!, accessible from all Rust code) ───────────────

impl Q {
    // ─── Field accessors (fields are pub(crate) to enforce invariants) ───────

    #[inline(always)]
    pub fn num(&self) -> i64 { self.num }

    #[inline(always)]
    pub fn den(&self) -> i64 { self.den }

    // ─── Constructors ───────────────────────────────────────────────────────

    #[inline(always)]
    pub fn zero() -> Q { Q { num: 0, den: 1 } }

    #[inline(always)]
    pub fn one() -> Q { Q { num: 1, den: 1 } }

    /// Exact conversion from i64. Returns None if |i| > BOUND.
    pub fn from_int(i: i64) -> Option<Q> {
        if i > BOUND || i < -BOUND {
            None
        } else {
            Some(Q { num: i, den: 1 })
        }
    }

    // ─── Boundary constructors (spec §2.1) ──────────────────────────────────

    /// Exact decimal ingestion: `from_decimal(85, 2)` → 17/20 = 0.85.
    /// Returns None if dec_places ≥ 20 or result exceeds BOUND.
    #[inline]
    pub fn from_decimal(mantissa: i64, dec_places: u8) -> Option<Q> {
        crate::convert::from_decimal(mantissa, dec_places)
    }

    /// Convert f64 to Q with directed rounding via integer bit-decomposition.
    /// Returns None on NaN, ±inf, or |v| > 2^61.
    /// Implementation touches no float arithmetic — stays in the verified region.
    #[inline]
    pub fn from_f64_dir(v: f64, dir: Dir) -> Option<Q> {
        crate::convert::from_f64_dir(v, dir)
    }

    /// Convert Q to f64 for display / DTO purposes ONLY.
    /// This is the single trusted boundary (see TRUSTED.md). Never feed back
    /// the result into Q arithmetic.
    #[inline]
    pub fn to_f64(self) -> f64 {
        crate::convert::to_f64(self)
    }

    /// Canonicalize (num, den): sign to den>0, GCD-reduce. None if den==0.
    pub fn new(num: i64, den: i64) -> Option<Q> {
        if den == 0 {
            return None;
        }
        let (n, d) = if den < 0 { (-num, -den) } else { (num, den) };
        let g = gcd_exec(
            (if n < 0 { -n } else { n }) as u64,
            d as u64,
        ) as i64;
        let num_r = n / g;
        let den_r = d / g;
        if num_r == 0 {
            Some(Q { num: 0, den: 1 })
        } else {
            Some(Q { num: num_r, den: den_r })
        }
    }

    // ─── Predicates ─────────────────────────────────────────────────────────

    #[inline(always)]
    pub fn is_zero(&self) -> bool { self.num == 0 }

    #[inline(always)]
    pub fn is_one(&self) -> bool { self.num == 1 && self.den == 1 }

    /// True iff 0 ≤ self ≤ 1.
    #[inline(always)]
    pub fn in_unit_interval(&self) -> bool {
        self.num >= 0 && self.num <= self.den
    }

    pub fn signum(&self) -> i64 {
        if self.num < 0 { -1 } else if self.num == 0 { 0 } else { 1 }
    }

    // ─── Arithmetic ─────────────────────────────────────────────────────────

    /// Negate. Always exact.
    pub fn neg(self) -> Q { Q { num: -self.num, den: self.den } }

    /// Absolute value. Always exact.
    pub fn abs(self) -> Q {
        if self.num < 0 { self.neg() } else { self }
    }

    /// Reciprocal. Requires self != 0.
    pub fn recip(self) -> Q {
        debug_assert!(!self.is_zero(), "recip of zero");
        if self.num > 0 {
            Q { num: self.den, den: self.num }
        } else {
            Q { num: -self.den, den: -self.num }
        }
    }

    /// Add. Exact in i128; rounds to budget if needed.
    pub fn add(self, other: Q) -> Q {
        let n = self.num as i128 * other.den as i128
              + other.num as i128 * self.den as i128;
        let d = self.den as i128 * other.den as i128;
        q_from_i128(n, d, Dir::Nearest)
    }

    /// Subtract. Exact in i128; rounds to budget if needed.
    pub fn sub(self, other: Q) -> Q {
        let n = self.num as i128 * other.den as i128
              - other.num as i128 * self.den as i128;
        let d = self.den as i128 * other.den as i128;
        q_from_i128(n, d, Dir::Nearest)
    }

    /// Multiply. Exact in i128; rounds to budget if needed.
    pub fn mul(self, other: Q) -> Q {
        let n = self.num as i128 * other.num as i128;
        let d = self.den as i128 * other.den as i128;
        q_from_i128(n, d, Dir::Nearest)
    }

    /// Divide. Returns None if other == 0.
    pub fn checked_div(self, other: Q) -> Option<Q> {
        if other.is_zero() { None } else { Some(self.div(other)) }
    }

    /// Divide. Precondition: other != 0 (statically ensured by Verus).
    pub fn div(self, other: Q) -> Q {
        debug_assert!(!other.is_zero(), "div by zero");
        let n = self.num as i128 * other.den as i128;
        let d = self.den as i128 * other.num as i128;
        q_from_i128(n, d, Dir::Nearest)
    }

    // ─── Comparison ─────────────────────────────────────────────────────────

    /// Exact cross-multiplication comparison. Safe: products fit i128 under I2.
    pub fn cmp_q(&self, other: &Q) -> core::cmp::Ordering {
        // |num_i| ≤ 2^62-1, den_i ≤ 2^62-1, product ≤ (2^62-1)^2 < 2^124 — fits i128.
        let lhs = self.num as i128 * other.den as i128;
        let rhs = other.num as i128 * self.den as i128;
        lhs.cmp(&rhs)
    }

    pub fn eq_q(&self, other: &Q) -> bool {
        self.num as i128 * other.den as i128 == other.num as i128 * self.den as i128
    }

    pub fn lt_q(&self, other: &Q) -> bool {
        (self.num as i128 * other.den as i128) < (other.num as i128 * self.den as i128)
    }

    pub fn le_q(&self, other: &Q) -> bool {
        (self.num as i128 * other.den as i128) <= (other.num as i128 * self.den as i128)
    }

    // ─── Min / max / clamp ───────────────────────────────────────────────────

    pub fn min_q(self, other: Q) -> Q {
        if self.lt_q(&other) { self } else { other }
    }

    pub fn max_q(self, other: Q) -> Q {
        if self.lt_q(&other) { other } else { self }
    }

    pub fn clamp_q(self, lo: Q, hi: Q) -> Q {
        debug_assert!(lo.le_q(&hi), "clamp: lo > hi");
        if self.lt_q(&lo) { lo }
        else if self.lt_q(&hi) { self }
        else { hi }
    }

    // ─── n-ary helpers ───────────────────────────────────────────────────────

    pub fn sum(slice: &[Q]) -> Q {
        let mut acc = Q::zero();
        for &q in slice {
            acc = acc.add(q);
        }
        acc
    }

    pub fn product(slice: &[Q]) -> Q {
        let mut acc = Q::one();
        for &q in slice {
            acc = acc.mul(q);
        }
        acc
    }

    pub fn weighted_mean(pairs: &[(Q, Q)]) -> Option<Q> {
        if pairs.is_empty() {
            return None;
        }
        let mut num_acc = Q::zero();
        let mut den_acc = Q::zero();
        for &(v, w) in pairs {
            num_acc = num_acc.add(v.mul(w));
            den_acc = den_acc.add(w);
        }
        if den_acc.is_zero() { None } else { Some(num_acc.div(den_acc)) }
    }
}

// ─── Internal: build Q from i128 (n, d), d > 0, reduce, round ───────────────

/// Build a canonical, bounded Q from i128 numerator and positive denominator.
/// If d < 0, the sign is absorbed here (for div: other.num could be negative).
#[inline]
pub(crate) fn q_from_i128(n: i128, d: i128, dir: Dir) -> Q {
    // Normalize sign so denominator is positive.
    let (n, d) = if d < 0 { (-n, -d) } else { (n, d) };
    debug_assert!(d > 0, "q_from_i128: den must be positive after sign fix");
    if n == 0 {
        return Q { num: 0, den: 1 };
    }
    let abs_n = if n < 0 { -n } else { n } as u64;
    let g = gcd_exec(abs_n, d as u64) as i128;
    let num_r = n / g;
    let den_r = d / g;
    if num_r >= -(BOUND as i128) && num_r <= BOUND as i128 && den_r <= BOUND as i128 {
        Q { num: num_r as i64, den: den_r as i64 }
    } else {
        round_to_budget(num_r, den_r, dir)
    }
}

// ─── Standard trait impls ──────────────────────────────────────────────────

impl PartialEq for Q {
    fn eq(&self, other: &Self) -> bool {
        self.num == other.num && self.den == other.den
    }
}

impl Eq for Q {}

impl PartialOrd for Q {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Q {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.cmp_q(other)
    }
}

impl core::hash::Hash for Q {
    fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        self.num.hash(state);
        self.den.hash(state);
    }
}

impl core::fmt::Display for Q {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}/{}", self.num, self.den)
    }
}

impl core::fmt::Debug for Q {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "Q({}/{})", self.num, self.den)
    }
}

// ─── Tests ────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    fn q(n: i64, d: i64) -> Q { Q::new(n, d).unwrap() }

    #[test]
    fn constructors() {
        let z = Q::zero();
        assert_eq!(z.num, 0); assert_eq!(z.den, 1);
        let o = Q::one();
        assert_eq!(o.num, 1); assert_eq!(o.den, 1);
    }

    #[test]
    fn canonical() {
        let a = q(6, 4);
        assert_eq!(a.num, 3); assert_eq!(a.den, 2);
        let b = q(-6, -4);
        assert_eq!(b.num, 3); assert_eq!(b.den, 2);
        let c = q(6, -4);
        assert_eq!(c.num, -3); assert_eq!(c.den, 2);
        assert_eq!(Q::new(0, 5).unwrap().den, 1);
    }

    #[test]
    fn arithmetic_exact() {
        let a = q(1, 2);
        let b = q(1, 3);
        assert_eq!(a.add(b), q(5, 6));
        assert_eq!(a.mul(b), q(1, 6));
        assert_eq!(a.div(b), q(3, 2));
        assert_eq!(a.sub(b), q(1, 6));
    }

    #[test]
    fn comparison() {
        let a = q(1, 3);
        let b = q(1, 2);
        assert!(a < b);
        assert!(b > a);
        assert_eq!(a, q(2, 6));
    }

    #[test]
    fn neg_abs_recip() {
        let a = q(3, 4);
        assert_eq!(a.neg(), q(-3, 4));
        assert_eq!(a.neg().abs(), a);
        assert_eq!(a.recip(), q(4, 3));
        assert_eq!(a.neg().recip(), q(-4, 3));
    }

    #[test]
    fn clamp() {
        let lo = q(0, 1);
        let hi = q(1, 1);
        assert_eq!(q(3, 2).clamp_q(lo, hi), hi);
        assert_eq!(q(-1, 2).clamp_q(lo, hi), lo);
        assert_eq!(q(1, 2).clamp_q(lo, hi), q(1, 2));
    }

    #[test]
    fn sum_product() {
        let vals = vec![q(1,2), q(1,3), q(1,6)];
        assert_eq!(Q::sum(&vals), Q::one());
        let vals2 = vec![q(2,1), q(3,1)];
        assert_eq!(Q::product(&vals2), q(6,1));
    }

    #[test]
    fn from_int_bounds() {
        assert!(Q::from_int(BOUND).is_some());
        assert!(Q::from_int(-BOUND).is_some());
        assert!(Q::from_int(i64::MIN).is_none());
        assert!(Q::from_int(i64::MAX).is_none());
    }
}
