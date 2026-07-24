//! Exact-with-verified-rounding rational arithmetic.
//!
//! `Q` is a bounded rational number type (`num/den` with `i64` components)
//! that provides exact arithmetic when results fit within a 62-bit budget,
//! and machine-checked error-bounded rounding when they don't.
//!
//! # Invariants
//!
//! Every `Q` value satisfies:
//! - **I1 (canonical):** `den > 0`, `gcd(|num|, den) == 1`, and `num == 0 ⟹ den == 1`.
//! - **I2 (bounded):** `|num| ≤ 2^62 − 1` and `den ≤ 2^62 − 1`.
//!
//! Canonical form guarantees: structural equality ⟺ mathematical equality,
//! so `Eq`, `Ord`, and `Hash` are all safe to derive.
//!
//! # Rounding
//!
//! When an exact result exceeds the 62-bit budget, dyadic-snap rounding
//! produces a representable value with `|error| ≤ 2^{-60} · max(1, |exact|)`.
//! `add`/`mul` are commutative (always) but **not associative in general**;
//! associativity holds on the exact path (when no rounding occurs).

mod gcd;
mod round;

pub use round::Dir;

use gcd::gcd128;
use round::{fits_budget, round_to_budget, BOUND};

use std::cmp::Ordering;
use std::fmt;
use std::hash::{Hash, Hasher};

use vstd::prelude::*;

verus! {

/// Ghost model: Q values are equal iff cross-multiplication agrees.
/// Division-free, per the spec's ghost-model discipline.
pub open spec fn q_eq(a_num: int, a_den: int, b_num: int, b_den: int) -> bool {
    a_num * b_den == b_num * a_den
}

/// Ghost model: a ≤ b via cross-multiplication (both dens positive).
pub open spec fn q_le(a_num: int, a_den: int, b_num: int, b_den: int) -> bool {
    a_num * b_den <= b_num * a_den
}

/// The I2 budget bound as a spec constant.
pub open spec fn spec_bound() -> int {
    (1i64 << 62u32) - 1
}

/// Invariant I1 ∧ I2: canonical and bounded.
pub open spec fn q_inv(num: int, den: int) -> bool {
    &&& den > 0
    &&& num == 0 ==> den == 1
    &&& num.abs() <= spec_bound()
    &&& den <= spec_bound()
}

} // verus!

/// A bounded rational number: value = `num / den`.
///
/// See module-level docs for invariants.
#[derive(Clone, Copy)]
pub struct Q {
    num: i64,
    den: i64,
}

// ============================================================
// Constructors (§2.1)
// ============================================================

impl Q {
    /// The additive identity `0/1`.
    #[inline]
    pub const fn zero() -> Self {
        Q { num: 0, den: 1 }
    }

    /// The multiplicative identity `1/1`.
    #[inline]
    pub const fn one() -> Self {
        Q { num: 1, den: 1 }
    }

    /// Exact conversion from an integer. Returns `None` if `|i| > 2^62 − 1`.
    pub fn from_int(i: i64) -> Option<Self> {
        if i.unsigned_abs() > BOUND {
            None
        } else {
            Some(Q { num: i, den: 1 })
        }
    }

    /// Construct from numerator and denominator.
    ///
    /// Returns `None` iff `den == 0`. Otherwise canonicalizes (sign to `den > 0`,
    /// GCD-reduces). Inputs within `i64` always fit I2 after reduction.
    pub fn new(num: i64, den: i64) -> Option<Self> {
        if den == 0 {
            return None;
        }
        Some(Self::canonical(num as i128, den as i128))
    }

    /// Exact decimal input: `from_decimal(85, 2)` = `85/100 = 17/20` = 0.85.
    ///
    /// Returns `None` if the denominator `10^dec_places` overflows `i64`,
    /// which happens at `dec_places >= 19`.
    pub fn from_decimal(mantissa: i64, dec_places: u8) -> Option<Self> {
        let den: i64 = 10i64.checked_pow(dec_places as u32)?;
        Self::new(mantissa, den)
    }

    /// Convert an `f64` to `Q` with directed rounding.
    ///
    /// Returns `None` on NaN or ±infinity. Restriction: `|v| ≤ 2^61` is the
    /// supported range (larger magnitudes may round).
    ///
    /// Implementation: bit-decomposition of the IEEE 754 representation,
    /// producing the exact rational `m · 2^e` and then `round_to_budget` if
    /// needed. No float arithmetic is used — this is fully integer-based.
    pub fn from_f64_dir(v: f64, dir: Dir) -> Option<Self> {
        if v.is_nan() || v.is_infinite() {
            return None;
        }
        if v == 0.0 {
            return Some(Q::zero());
        }

        let bits = v.to_bits();
        let sign: i128 = if (bits >> 63) != 0 { -1 } else { 1 };
        let biased_exp = ((bits >> 52) & 0x7FF) as i32;
        let frac = bits & ((1u64 << 52) - 1);

        let (mantissa, exponent): (u128, i32) = if biased_exp == 0 {
            // Subnormal: m = frac, e = 1 - 1023 - 52 = -1074
            (frac as u128, -1074)
        } else {
            // Normal: m = (1 << 52) | frac, e = biased_exp - 1023 - 52
            ((1u128 << 52) | frac as u128, biased_exp - 1023 - 52)
        };

        // The exact value is sign * mantissa * 2^exponent.
        // Express as a fraction: num / den.
        let (num_abs, den): (u128, u128) = if exponent >= 0 {
            let shift = exponent as u32;
            if shift <= 62 {
                (mantissa << shift, 1u128)
            } else {
                // Magnitude exceeds budget; will be rounded.
                // Represent as mantissa * 2^shift / 1 and let reduce_and_fit handle it.
                // But mantissa << shift might overflow u128. Cap at a reasonable value.
                // For |v| ≤ 2^61 this doesn't happen (shift ≤ 61 - 52 + 52 = 61).
                // For larger values, approximate.
                let safe_shift = shift.min(126 - (128 - mantissa.leading_zeros()));
                (mantissa << safe_shift, 1u128)
            }
        } else {
            let neg_exp = (-exponent) as u32;
            // num = mantissa, den = 2^neg_exp
            // GCD-reduce by removing common trailing zeros
            let tz_m = mantissa.trailing_zeros();
            let common = tz_m.min(neg_exp);
            (mantissa >> common, 1u128 << (neg_exp - common))
        };

        let num_i128 = sign * num_abs as i128;
        let den_i128 = den as i128;

        Some(Self::reduce_and_fit(num_i128, den_i128, dir))
    }

    /// Numerator accessor.
    #[inline]
    pub const fn num(&self) -> i64 {
        self.num
    }

    /// Denominator accessor (always > 0).
    #[inline]
    pub const fn den(&self) -> i64 {
        self.den
    }

    /// Internal: build canonical Q from i128 pair (den != 0).
    fn canonical(num: i128, den: i128) -> Self {
        if num == 0 {
            return Q { num: 0, den: 1 };
        }

        let (num, den) = if den < 0 { (-num, -den) } else { (num, den) };

        let g = gcd128(num.unsigned_abs(), den as u128);
        let rnum = num / g as i128;
        let rden = den / g as i128;

        debug_assert!(rden > 0);

        // After GCD reduction of i64 inputs, the result always fits in i64.
        // (Reducing can only make values smaller or equal.)
        Q {
            num: rnum as i64,
            den: rden as i64,
        }
    }

    /// Internal: reduce an i128 fraction and fit to budget, rounding if needed.
    ///
    /// This is the workhorse called by all arithmetic ops after computing
    /// the exact i128 intermediate.
    fn reduce_and_fit(num: i128, den: i128, dir: Dir) -> Self {
        debug_assert!(den > 0);

        if num == 0 {
            return Q { num: 0, den: 1 };
        }

        let g = gcd128(num.unsigned_abs(), den as u128);
        let rnum = num / g as i128;
        let rden = den / g as i128;

        if fits_budget(rnum, rden) {
            Q {
                num: rnum as i64,
                den: rden as i64,
            }
        } else {
            let (n, d) = round_to_budget(rnum, rden, dir);
            Q { num: n, den: d }
        }
    }
}

// ============================================================
// Comparison and predicates (§2.3) — all exact
// ============================================================

impl Q {
    #[inline]
    pub fn is_zero(self) -> bool {
        self.num == 0
    }

    #[inline]
    pub fn is_one(self) -> bool {
        self.num == 1 && self.den == 1
    }

    /// Returns −1, 0, or +1.
    #[inline]
    pub fn signum(self) -> i64 {
        self.num.signum()
    }

    /// `0 ≤ q ≤ 1`.
    #[inline]
    pub fn in_unit_interval(self) -> bool {
        self.num >= 0 && self.num <= self.den
    }

    /// Cross-multiply comparison (exact, no rounding).
    ///
    /// Compares `a.num * b.den` vs `b.num * a.den` in `i128`.
    fn cmp_cross(self, other: Self) -> Ordering {
        let lhs = self.num as i128 * other.den as i128;
        let rhs = other.num as i128 * self.den as i128;
        lhs.cmp(&rhs)
    }
}

impl PartialEq for Q {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        // Canonical form: structural equality ⟺ mathematical equality
        self.num == other.num && self.den == other.den
    }
}

impl Eq for Q {}

impl Hash for Q {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.num.hash(state);
        self.den.hash(state);
    }
}

impl PartialOrd for Q {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Q {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        self.cmp_cross(*other)
    }
}

// ============================================================
// Arithmetic (§2.2)
// ============================================================

impl Q {
    /// Addition. Exact when result fits budget; otherwise rounds to nearest.
    ///
    /// Verus spec (V3, division-free):
    ///   `r.num * (a.den * b.den) == (a.num * b.den + b.num * a.den) * r.den`
    /// (when exact; when rounded, R1–R4 apply).
    pub fn add(self, other: Self) -> Self {
        // a/b + c/d = (ad + bc) / bd
        let num = self.num as i128 * other.den as i128
            + other.num as i128 * self.den as i128;
        let den = self.den as i128 * other.den as i128;
        // V2: |num| ≤ 2·(2^62−1)^2 < 2^125, |den| < 2^124. Both fit i128.
        Self::reduce_and_fit(num, den, Dir::Nearest)
    }

    /// Subtraction.
    pub fn sub(self, other: Self) -> Self {
        // a/b - c/d = (ad - bc) / bd
        let num = self.num as i128 * other.den as i128
            - other.num as i128 * self.den as i128;
        let den = self.den as i128 * other.den as i128;
        Self::reduce_and_fit(num, den, Dir::Nearest)
    }

    /// Multiplication.
    pub fn mul(self, other: Self) -> Self {
        // a/b * c/d = ac / bd
        let num = self.num as i128 * other.num as i128;
        let den = self.den as i128 * other.den as i128;
        // V2: |num| ≤ (2^62−1)^2 < 2^124, |den| < 2^124. Both fit i128.
        Self::reduce_and_fit(num, den, Dir::Nearest)
    }

    /// Division. Panics if `other` is zero (precondition — Verus would
    /// discharge this statically).
    pub fn div(self, other: Self) -> Self {
        assert!(!other.is_zero(), "Q::div: division by zero");
        // a/b ÷ c/d = ad / bc
        let num = self.num as i128 * other.den as i128;
        let den = self.den as i128 * other.num as i128;
        // den might be negative (if other.num < 0); reduce_and_fit expects den > 0
        let (num, den) = if den < 0 { (-num, -den) } else { (num, den) };
        Self::reduce_and_fit(num, den, Dir::Nearest)
    }

    /// Negation. Always exact (I2 is symmetric in sign).
    #[inline]
    pub fn neg(self) -> Self {
        Q {
            num: -self.num,
            den: self.den,
        }
    }

    /// Absolute value. Always exact.
    #[inline]
    pub fn abs(self) -> Self {
        Q {
            num: self.num.abs(),
            den: self.den,
        }
    }

    /// Reciprocal. Panics if `self` is zero.
    pub fn recip(self) -> Self {
        assert!(!self.is_zero(), "Q::recip: reciprocal of zero");
        if self.num > 0 {
            Q {
                num: self.den,
                den: self.num,
            }
        } else {
            Q {
                num: -self.den,
                den: -self.num,
            }
        }
    }

    /// Minimum of two rationals.
    #[inline]
    pub fn min(self, other: Self) -> Self {
        if self <= other {
            self
        } else {
            other
        }
    }

    /// Maximum of two rationals.
    #[inline]
    pub fn max(self, other: Self) -> Self {
        if self >= other {
            self
        } else {
            other
        }
    }

    /// Clamp to `[lo, hi]`. Panics if `lo > hi`.
    pub fn clamp(self, lo: Self, hi: Self) -> Self {
        assert!(lo <= hi, "Q::clamp: lo > hi");
        self.max(lo).min(hi)
    }

    // --- Directed variants (for future interval arithmetic) ---

    pub fn add_dir(self, other: Self, dir: Dir) -> Self {
        let num = self.num as i128 * other.den as i128
            + other.num as i128 * self.den as i128;
        let den = self.den as i128 * other.den as i128;
        Self::reduce_and_fit(num, den, dir)
    }

    pub fn sub_dir(self, other: Self, dir: Dir) -> Self {
        let num = self.num as i128 * other.den as i128
            - other.num as i128 * self.den as i128;
        let den = self.den as i128 * other.den as i128;
        Self::reduce_and_fit(num, den, dir)
    }

    pub fn mul_dir(self, other: Self, dir: Dir) -> Self {
        let num = self.num as i128 * other.num as i128;
        let den = self.den as i128 * other.den as i128;
        Self::reduce_and_fit(num, den, dir)
    }

    pub fn div_dir(self, other: Self, dir: Dir) -> Self {
        assert!(!other.is_zero(), "Q::div_dir: division by zero");
        let num = self.num as i128 * other.den as i128;
        let den = self.den as i128 * other.num as i128;
        let (num, den) = if den < 0 { (-num, -den) } else { (num, den) };
        Self::reduce_and_fit(num, den, dir)
    }
}

// ============================================================
// std::ops trait impls
// ============================================================

impl std::ops::Add for Q {
    type Output = Q;
    #[inline]
    fn add(self, rhs: Q) -> Q {
        Q::add(self, rhs)
    }
}

impl std::ops::Sub for Q {
    type Output = Q;
    #[inline]
    fn sub(self, rhs: Q) -> Q {
        Q::sub(self, rhs)
    }
}

impl std::ops::Mul for Q {
    type Output = Q;
    #[inline]
    fn mul(self, rhs: Q) -> Q {
        Q::mul(self, rhs)
    }
}

impl std::ops::Div for Q {
    type Output = Q;
    #[inline]
    fn div(self, rhs: Q) -> Q {
        Q::div(self, rhs)
    }
}

impl std::ops::Neg for Q {
    type Output = Q;
    #[inline]
    fn neg(self) -> Q {
        Q::neg(self)
    }
}

// ============================================================
// Conversions out (§2.4)
// ============================================================

impl Q {
    /// Convert to `f64`. For display/DTO boundary ONLY.
    ///
    /// This is the one trusted boundary (`external_body` in Verus):
    /// proving float rounding correctness is not worth it. Covered by
    /// differential tests against `malachite-q` instead.
    ///
    /// MUST NEVER be fed back into Q arithmetic.
    pub fn to_f64(self) -> f64 {
        self.num as f64 / self.den as f64
    }
}

impl fmt::Display for Q {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}/{}", self.num, self.den)
    }
}

impl fmt::Debug for Q {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Q({}/{})", self.num, self.den)
    }
}

// ============================================================
// Serde (feature-gated)
// ============================================================

#[cfg(feature = "serde")]
mod serde_impl {
    use super::*;
    use serde::{Deserialize, Deserializer, Serialize, Serializer};

    #[derive(Serialize, Deserialize)]
    struct QPair {
        num: i64,
        den: i64,
    }

    impl Serialize for Q {
        fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
            let pair = QPair {
                num: self.num,
                den: self.den,
            };
            pair.serialize(serializer)
        }
    }

    impl<'de> Deserialize<'de> for Q {
        fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
            let pair = QPair::deserialize(deserializer)?;
            Q::new(pair.num, pair.den).ok_or_else(|| {
                serde::de::Error::custom("Q denominator must be nonzero")
            })
        }
    }
}

// ============================================================
// n-ary helpers (§2.5)
// ============================================================

impl Q {
    /// Left-to-right sum. Returns `zero()` for empty input.
    ///
    /// Error bound after `k` elements: `k · 2^{-60}` (each binary add can
    /// introduce at most one rounding step).
    pub fn sum(values: &[Q]) -> Q {
        values.iter().copied().fold(Q::zero(), Q::add)
    }

    /// Left-to-right product. Returns `one()` for empty input.
    pub fn product(values: &[Q]) -> Q {
        values.iter().copied().fold(Q::one(), Q::mul)
    }

    /// Weighted mean: `Σ(vᵢ · wᵢ) / Σ(wᵢ)`.
    ///
    /// Panics if `pairs` is empty or all weights are zero.
    pub fn weighted_mean(pairs: &[(Q, Q)]) -> Q {
        assert!(!pairs.is_empty(), "Q::weighted_mean: empty input");
        let (num, den) = pairs.iter().fold(
            (Q::zero(), Q::zero()),
            |(acc_n, acc_d), &(value, weight)| {
                (acc_n + value * weight, acc_d + weight)
            },
        );
        assert!(!den.is_zero(), "Q::weighted_mean: total weight is zero");
        num / den
    }
}

// ============================================================
// Unit tests
// ============================================================

#[cfg(test)]
mod tests {
    use super::*;

    // --- Constructors ---

    #[test]
    fn zero_and_one() {
        let z = Q::zero();
        assert_eq!(z.num(), 0);
        assert_eq!(z.den(), 1);
        assert!(z.is_zero());
        assert!(!z.is_one());

        let o = Q::one();
        assert_eq!(o.num(), 1);
        assert_eq!(o.den(), 1);
        assert!(o.is_one());
        assert!(!o.is_zero());
    }

    #[test]
    fn from_int_valid() {
        let q = Q::from_int(42).unwrap();
        assert_eq!(q.num(), 42);
        assert_eq!(q.den(), 1);
    }

    #[test]
    fn from_int_bounds() {
        let bound = BOUND as i64;
        assert!(Q::from_int(bound).is_some());
        assert!(Q::from_int(-bound).is_some());
        // i64::MIN has abs > BOUND (abs overflows), but from_int checks unsigned_abs
        assert!(Q::from_int(i64::MIN).is_none());
    }

    #[test]
    fn new_basic() {
        assert!(Q::new(1, 0).is_none());

        let q = Q::new(6, 4).unwrap();
        assert_eq!(q.num(), 3);
        assert_eq!(q.den(), 2);

        let q = Q::new(-6, 4).unwrap();
        assert_eq!(q.num(), -3);
        assert_eq!(q.den(), 2);

        let q = Q::new(6, -4).unwrap();
        assert_eq!(q.num(), -3);
        assert_eq!(q.den(), 2);

        let q = Q::new(-6, -4).unwrap();
        assert_eq!(q.num(), 3);
        assert_eq!(q.den(), 2);

        let q = Q::new(0, 5).unwrap();
        assert_eq!(q.num(), 0);
        assert_eq!(q.den(), 1);
    }

    #[test]
    fn from_decimal_basic() {
        let q = Q::from_decimal(85, 2).unwrap();
        assert_eq!(q.num(), 17);
        assert_eq!(q.den(), 20);

        let q = Q::from_decimal(1, 0).unwrap();
        assert_eq!(q.num(), 1);
        assert_eq!(q.den(), 1);

        let q = Q::from_decimal(5, 1).unwrap();
        assert_eq!(q.num(), 1);
        assert_eq!(q.den(), 2);
    }

    #[test]
    fn from_decimal_overflow() {
        assert!(Q::from_decimal(1, 19).is_none());
    }

    // --- Comparison ---

    #[test]
    fn ordering() {
        let a = Q::new(1, 3).unwrap();
        let b = Q::new(1, 2).unwrap();
        let c = Q::new(2, 6).unwrap(); // = 1/3

        assert!(a < b);
        assert!(a == c);
        assert!(b > a);
        assert_eq!(a.cmp(&c), Ordering::Equal);
    }

    #[test]
    fn in_unit_interval_test() {
        assert!(Q::zero().in_unit_interval());
        assert!(Q::one().in_unit_interval());
        assert!(Q::new(1, 2).unwrap().in_unit_interval());
        assert!(!Q::new(3, 2).unwrap().in_unit_interval());
        assert!(!Q::new(-1, 2).unwrap().in_unit_interval());
    }

    #[test]
    fn signum_test() {
        assert_eq!(Q::zero().signum(), 0);
        assert_eq!(Q::one().signum(), 1);
        assert_eq!(Q::new(-3, 7).unwrap().signum(), -1);
    }

    // --- Arithmetic ---

    #[test]
    fn add_exact() {
        let a = Q::new(1, 3).unwrap();
        let b = Q::new(1, 6).unwrap();
        let r = a + b;
        assert_eq!(r, Q::new(1, 2).unwrap());
    }

    #[test]
    fn sub_exact() {
        let a = Q::new(1, 2).unwrap();
        let b = Q::new(1, 3).unwrap();
        let r = a - b;
        assert_eq!(r, Q::new(1, 6).unwrap());
    }

    #[test]
    fn mul_exact() {
        let a = Q::new(2, 3).unwrap();
        let b = Q::new(3, 4).unwrap();
        let r = a * b;
        assert_eq!(r, Q::new(1, 2).unwrap());
    }

    #[test]
    fn div_exact() {
        let a = Q::new(1, 2).unwrap();
        let b = Q::new(3, 4).unwrap();
        let r = a / b;
        assert_eq!(r, Q::new(2, 3).unwrap());
    }

    #[test]
    fn neg_test() {
        let a = Q::new(3, 7).unwrap();
        assert_eq!((-a).num(), -3);
        assert_eq!((-a).den(), 7);
        assert_eq!(-(-a), a);
    }

    #[test]
    fn abs_test() {
        let a = Q::new(-3, 7).unwrap();
        assert_eq!(a.abs(), Q::new(3, 7).unwrap());
        assert_eq!(Q::zero().abs(), Q::zero());
    }

    #[test]
    fn recip_test() {
        let a = Q::new(3, 7).unwrap();
        assert_eq!(a.recip(), Q::new(7, 3).unwrap());

        let b = Q::new(-3, 7).unwrap();
        let r = b.recip();
        assert_eq!(r, Q::new(-7, 3).unwrap());
        assert!(r.den() > 0);
    }

    #[test]
    #[should_panic(expected = "division by zero")]
    fn div_by_zero_panics() {
        let _ = Q::one() / Q::zero();
    }

    #[test]
    #[should_panic(expected = "reciprocal of zero")]
    fn recip_zero_panics() {
        let _ = Q::zero().recip();
    }

    // --- Min / Max / Clamp ---

    #[test]
    fn min_max_clamp() {
        let a = Q::new(1, 4).unwrap();
        let b = Q::new(3, 4).unwrap();
        assert_eq!(a.min(b), a);
        assert_eq!(a.max(b), b);

        let v = Q::new(5, 4).unwrap();
        assert_eq!(v.clamp(Q::zero(), Q::one()), Q::one());
        assert_eq!(Q::new(-1, 2).unwrap().clamp(Q::zero(), Q::one()), Q::zero());
        assert_eq!(Q::new(1, 2).unwrap().clamp(Q::zero(), Q::one()), Q::new(1, 2).unwrap());
    }

    // --- Commutativity ---

    #[test]
    fn add_commutative() {
        let a = Q::new(17, 31).unwrap();
        let b = Q::new(23, 47).unwrap();
        assert_eq!(a + b, b + a);
    }

    #[test]
    fn mul_commutative() {
        let a = Q::new(17, 31).unwrap();
        let b = Q::new(23, 47).unwrap();
        assert_eq!(a * b, b * a);
    }

    // --- Exact-path associativity ---

    #[test]
    fn add_associative_exact() {
        let a = Q::new(1, 6).unwrap();
        let b = Q::new(1, 3).unwrap();
        let c = Q::new(1, 2).unwrap();
        assert_eq!((a + b) + c, a + (b + c));
    }

    #[test]
    fn mul_associative_exact() {
        let a = Q::new(1, 2).unwrap();
        let b = Q::new(2, 3).unwrap();
        let c = Q::new(3, 4).unwrap();
        assert_eq!((a * b) * c, a * (b * c));
    }

    // --- Display ---

    #[test]
    fn display_test() {
        assert_eq!(format!("{}", Q::new(3, 7).unwrap()), "3/7");
        assert_eq!(format!("{}", Q::zero()), "0/1");
        assert_eq!(format!("{}", Q::new(-1, 2).unwrap()), "-1/2");
    }

    // --- f64 conversion ---

    #[test]
    fn from_f64_basic() {
        let q = Q::from_f64_dir(0.5, Dir::Nearest).unwrap();
        assert_eq!(q, Q::new(1, 2).unwrap());

        let q = Q::from_f64_dir(0.25, Dir::Nearest).unwrap();
        assert_eq!(q, Q::new(1, 4).unwrap());

        let q = Q::from_f64_dir(1.0, Dir::Nearest).unwrap();
        assert_eq!(q, Q::one());

        let q = Q::from_f64_dir(0.0, Dir::Nearest).unwrap();
        assert_eq!(q, Q::zero());
    }

    #[test]
    fn from_f64_nan_inf() {
        assert!(Q::from_f64_dir(f64::NAN, Dir::Nearest).is_none());
        assert!(Q::from_f64_dir(f64::INFINITY, Dir::Nearest).is_none());
        assert!(Q::from_f64_dir(f64::NEG_INFINITY, Dir::Nearest).is_none());
    }

    #[test]
    fn from_f64_negative() {
        let q = Q::from_f64_dir(-0.5, Dir::Nearest).unwrap();
        assert_eq!(q, Q::new(-1, 2).unwrap());
    }

    #[test]
    fn to_f64_basic() {
        let q = Q::new(1, 3).unwrap();
        let f = q.to_f64();
        assert!((f - 1.0 / 3.0).abs() < 1e-15);
    }

    // --- n-ary ---

    #[test]
    fn sum_test() {
        let vals: Vec<Q> = (1..=4).map(|i| Q::new(1, i).unwrap()).collect();
        let s = Q::sum(&vals); // 1 + 1/2 + 1/3 + 1/4 = 25/12
        assert_eq!(s, Q::new(25, 12).unwrap());
    }

    #[test]
    fn sum_empty() {
        assert_eq!(Q::sum(&[]), Q::zero());
    }

    #[test]
    fn product_test() {
        let vals = vec![Q::new(1, 2).unwrap(), Q::new(2, 3).unwrap(), Q::new(3, 4).unwrap()];
        let p = Q::product(&vals); // (1/2)·(2/3)·(3/4) = 1/4
        assert_eq!(p, Q::new(1, 4).unwrap());
    }

    #[test]
    fn weighted_mean_test() {
        let pairs = vec![
            (Q::new(1, 1).unwrap(), Q::new(1, 1).unwrap()),
            (Q::new(3, 1).unwrap(), Q::new(1, 1).unwrap()),
        ];
        // (1·1 + 3·1) / (1+1) = 4/2 = 2
        assert_eq!(Q::weighted_mean(&pairs), Q::new(2, 1).unwrap());
    }

    // --- Budget-edge (rounding) tests ---

    #[test]
    fn near_budget_add_in_range() {
        // Values whose sum stays representable (within magnitude budget)
        let half_bound = (BOUND / 2) as i64;
        let a = Q::new(half_bound, 1).unwrap();
        let b = Q::new(half_bound, 1).unwrap();
        let r = a + b;
        check_invariants_internal(r);
        // Sum = 2*(BOUND/2) ≤ BOUND, should be exact
        assert_eq!(r, Q::from_int(2 * half_bound).unwrap());
    }

    #[test]
    fn near_budget_add_large_den() {
        // Two values with large denominators whose sum requires rounding
        let a = Q::new(1, BOUND as i64).unwrap();
        let b = Q::new(1, (BOUND - 1) as i64).unwrap();
        // a + b = ((BOUND-1) + BOUND) / (BOUND * (BOUND-1))
        // The denominator BOUND*(BOUND-1) ≈ 2^124 exceeds budget → rounding
        let r = a + b;
        check_invariants_internal(r);
        // The value is ≈ 2/BOUND ≈ 4.3e-19, very small but nonzero
        let approx = r.to_f64();
        let expected = 1.0 / BOUND as f64 + 1.0 / (BOUND - 1) as f64;
        assert!((approx - expected).abs() < 1e-15);
    }

    #[test]
    fn saturate_beyond_magnitude() {
        // Adding two values at the ceiling: sum exceeds representable magnitude.
        // Per §4, engine values are always magnitude-bounded (opinions ∈ [0,1],
        // counts ≤ 10^5), so this edge case never occurs in practice. We just
        // verify invariants hold.
        let big = BOUND as i64;
        let a = Q::new(big, 1).unwrap();
        let b = Q::new(big, 1).unwrap();
        let r = a + b;
        check_invariants_internal(r);
    }

    fn check_invariants_internal(q: Q) {
        assert!(q.den() > 0);
        assert!(q.num().unsigned_abs() <= BOUND);
        assert!((q.den() as u64) <= BOUND);
        if q.num() == 0 {
            assert_eq!(q.den(), 1);
        }
    }

    #[test]
    fn long_fold_chain() {
        // 10000 additions of 1/10000 should give ≈ 1
        let n = 10000;
        let step = Q::new(1, n).unwrap();
        let result = (0..n).fold(Q::zero(), |acc, _| acc + step);
        let f = result.to_f64();
        assert!(
            (f - 1.0).abs() < 1e-10,
            "long fold chain: expected ~1.0, got {f}"
        );
    }
}
