//! # `the-q` — verified bounded rational (ℚ) arithmetic
//!
//! Exact-with-verified-rounding rational arithmetic over a fixed width budget,
//! intended as the deterministic numeric backbone of a subjective-logic fusion
//! engine. Values are stored canonically as `num / den` with `den > 0` and
//! `gcd(|num|, den) == 1`, so **structural equality is mathematical equality**
//! and every value has a single bit-exact representation.
//!
//! ## What "bounded rational with verified rounding" means
//!
//! Arithmetic is **exact** while numerator and denominator fit the budget
//! `2^62 − 1` (invariant [`I2`](#invariants)); when an exact result exceeds the
//! budget it is rounded to the budget grid with a **proven** directed error
//! bound (`|result − exact| ≤ 2^-60 · max(1, |exact|)`). All intermediate
//! computation happens in `i128`, which the budget guarantees never overflows
//! (see the module docs on [`Q::add`] etc.).
//!
//! ## Honesty consequence (read this)
//!
//! With rounding enabled, `add` and `mul` are **commutative** but **not
//! associative in general** — associativity and distributivity hold only on the
//! *exact path* (when no operand or result is rounded). Any computation whose
//! exact values all fit the budget is **end-to-end exact** (theorem R1); small
//! investigations therefore pay *zero* rounding. See `README.md` and the
//! rounding contract in the crate specification for the full statement.
//!
//! ## Verification
//!
//! The integer arithmetic in this crate is designed to be machine-checked by
//! [Verus](https://github.com/verus-lang/verus). The Verus specification and
//! proof scaffold live under `verus/`; the trusted float boundary is documented
//! in `TRUSTED.md`. The two float-touching functions ([`Q::to_f64`], and
//! optionally [`Q::from_f64_dir`]) are the only edges that are differentially
//! tested rather than proven.

#![cfg_attr(not(test), no_std)]
#![forbid(unsafe_code)]
// The public surface deliberately exposes inherent methods named `add`, `sub`,
// `mul`, `div`, `neg`, and `eq` (the operator traits are *also* implemented, for
// the `Nearest`-rounding sugar). The named methods are the primary, explicit API
// (they carry the directed variants and the div precondition), so this lint —
// which assumes such names should only come from the traits — does not apply.
#![allow(clippy::should_implement_trait)]

use core::cmp::Ordering;
use core::fmt;

/// The width budget: `|num| ≤ BUDGET` and `den ≤ BUDGET` for every canonical
/// [`Q`] (invariant I2). Chosen as `2^62 − 1` so that every `i128` intermediate
/// in add/sub/mul/div/compare is provably in range — a `2^63` budget would
/// overflow the add-numerator at `i128::MAX`.
pub const BUDGET: i64 = (1i64 << 62) - 1;

/// Rounding direction for directed operations (see [`Q::from_f64_dir`] and the
/// rounding contract). `Down` rounds toward −∞, `Up` toward +∞, `Nearest`
/// toward the closest grid point (ties away from zero).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Dir {
    /// Round toward −∞: result ≤ exact value.
    Down,
    /// Round toward +∞: result ≥ exact value.
    Up,
    /// Round to nearest grid point (ties away from zero).
    Nearest,
}

/// A canonical, bounded rational number `num / den`.
///
/// Invariants maintained by every public constructor and operation:
/// - **I1 (canonical):** `den > 0`, `gcd(|num|, den) == 1`, and `num == 0 ⟹ den == 1`.
/// - **I2 (bounded):** `|num| ≤ 2^62 − 1` and `den ≤ 2^62 − 1`.
///
/// Because the form is canonical, `PartialEq`/`Eq`/`Hash` are derived (safe:
/// structural equality ⟺ mathematical equality), while `Ord`/`PartialOrd` are
/// implemented by cross-multiplication so the ordering matches value order.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Q {
    num: i64,
    den: i64,
}

// ---------------------------------------------------------------------------
// Internal integer helpers (the verified region operates on these).
// ---------------------------------------------------------------------------

/// Euclid's algorithm on `u128` (superset of the `u64` GCD proven in Verus,
/// obligation V5). Terminates: the second argument strictly decreases each step
/// (measure), reaching 0.
#[inline]
fn gcd_u128(mut a: u128, mut b: u128) -> u128 {
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    a
}

/// Reduce a raw fraction to canonical form: `den > 0`, `gcd(|num|, den) == 1`,
/// `num == 0 ⟹ den == 1`. Operates in `i128` (all callers pass values that fit
/// `i128`). Panics only if `d == 0`, which every caller excludes.
#[inline]
fn reduce_i128(mut n: i128, mut d: i128) -> (i128, i128) {
    debug_assert!(d != 0);
    if d < 0 {
        n = -n;
        d = -d;
    }
    if n == 0 {
        return (0, 1);
    }
    let g = gcd_u128(n.unsigned_abs(), d as u128) as i128;
    (n / g, d / g)
}

const BUDGET_U128: u128 = (1u128 << 62) - 1;

/// Bit length of a positive `u128` (`0` for `0`).
#[inline]
fn bits(x: u128) -> u32 {
    128 - x.leading_zeros()
}

/// Compute `floor(num * 2^s / den)` and the leftover remainder, using bitwise
/// long division so no intermediate ever exceeds `u128`. Returns
/// `(quotient, remainder)` with `value * 2^s == quotient + remainder / den`,
/// `0 ≤ remainder < den`. Requires `num, den > 0`.
#[inline]
fn scaled_floor(num: u128, den: u128, s: u32) -> (u128, u128) {
    let mut q = num / den;
    let mut r = num % den; // r < den
    let mut i = 0;
    while i < s {
        // r < den ≤ 2^124, so r << 1 < 2^125 — no overflow.
        r <<= 1;
        let bit = if r >= den {
            r -= den;
            1
        } else {
            0
        };
        // q stays below the final numerator (~2^62) for every s we choose.
        q = (q << 1) | bit;
        i += 1;
    }
    (q, r)
}

/// The rounding step (obligation V4). Reduces `n / d` (with `d != 0`) and, if
/// the reduced fraction already satisfies I2, returns it **exactly** (R1).
/// Otherwise it snaps to the dyadic grid `p / 2^s` with `s` chosen per magnitude
/// so that the directed error is `≤ 2^-60 · max(1, |value|)` (R3), respecting
/// the requested direction (R2).
fn round_to_budget(n_raw: i128, d_raw: i128, dir: Dir) -> Q {
    let (n, d) = reduce_i128(n_raw, d_raw);
    // R1: exact when it already fits the budget.
    if n.unsigned_abs() <= BUDGET_U128 && (d as u128) <= BUDGET_U128 {
        return Q {
            num: n as i64,
            den: d as i64,
        };
    }
    if n == 0 {
        return Q::zero();
    }

    let sign_neg = n < 0;
    let mag_num = n.unsigned_abs();
    let mag_den = d as u128;

    // e is an upper estimate of floor(log2(|value|)): floor(log2 mag) ∈ {e-1, e}.
    // Using s = 61 - e guarantees p < 2^62 (fits BUDGET) and error ≤ 2^-60·|value|.
    let bn = bits(mag_num) as i64;
    let bd = bits(mag_den) as i64;
    let e = bn - bd;
    let mut s: i64 = (61 - e).clamp(0, 61);

    loop {
        let su = s as u32;
        let den_pow: u128 = 1u128 << su;
        let (q, rem) = scaled_floor(mag_num, mag_den, su);
        let has_rem = rem != 0;

        // Choose the magnitude-side numerator for the requested direction.
        // value = ± (q + rem/mag_den) / 2^s; lo-magnitude = q, hi-magnitude = q+1.
        let p: u128 = match dir {
            Dir::Down => {
                if sign_neg {
                    // need result ≤ value (more negative) ⟹ larger magnitude.
                    if has_rem {
                        q + 1
                    } else {
                        q
                    }
                } else {
                    q
                }
            }
            Dir::Up => {
                if sign_neg {
                    q
                } else if has_rem {
                    q + 1
                } else {
                    q
                }
            }
            Dir::Nearest => {
                // Compare 2*rem vs mag_den; tie (==) rounds away from zero (up in magnitude).
                let twice = rem << 1; // rem < den ≤ 2^124 ⟹ no overflow
                if twice >= mag_den && has_rem {
                    q + 1
                } else {
                    q
                }
            }
        };

        if p <= BUDGET_U128 && den_pow <= BUDGET_U128 {
            let num_signed = if sign_neg { -(p as i128) } else { p as i128 };
            let (rn, rd) = reduce_i128(num_signed, den_pow as i128);
            return Q {
                num: rn as i64,
                den: rd as i64,
            };
        }

        if s == 0 {
            // Value magnitude exceeds the representable ceiling (2^62 − 1). This
            // is outside the engine's value domain (opinions in [0,1], counts
            // ≤ 1e5); saturate to the budget extreme. Documented in TRUSTED.md.
            let sat = if sign_neg { -BUDGET } else { BUDGET };
            return Q { num: sat, den: 1 };
        }
        s -= 1;
    }
}

// ---------------------------------------------------------------------------
// Constructors (§2.1)
// ---------------------------------------------------------------------------

impl Q {
    /// The value `0` (`0/1`).
    #[inline]
    pub const fn zero() -> Q {
        Q { num: 0, den: 1 }
    }

    /// The value `1` (`1/1`).
    #[inline]
    pub const fn one() -> Q {
        Q { num: 1, den: 1 }
    }

    /// Exact integer, or `None` if `|i| > 2^62 − 1` (which includes `i64::MIN`,
    /// whose magnitude `2^63` exceeds the budget).
    #[inline]
    pub fn from_int(i: i64) -> Option<Q> {
        if i == i64::MIN || i.unsigned_abs() > BUDGET as u64 {
            return None;
        }
        Some(Q { num: i, den: 1 })
    }

    /// Construct `num / den`, canonicalized (sign moved to the denominator,
    /// GCD-reduced). Returns `None` if `den == 0`, or if the canonical form
    /// cannot satisfy the budget I2 (only possible when the reduced magnitude is
    /// `≥ 2^62`, e.g. `num = i64::MAX, den = 1` — outside the engine domain).
    ///
    /// > Note: the specification states "None iff `den == 0`". Because `i64`
    /// > spans `±(2^63 − 1)` — wider than the `2^62 − 1` budget — a canonical
    /// > form can legitimately exceed I2, so this constructor also returns
    /// > `None` in that case rather than fabricate a value that breaks the
    /// > invariant. Every input with `|value| < 2^62` after reduction is exact.
    #[inline]
    pub fn new(num: i64, den: i64) -> Option<Q> {
        if den == 0 {
            return None;
        }
        let (n, d) = reduce_i128(num as i128, den as i128);
        if n.unsigned_abs() <= BUDGET_U128 && (d as u128) <= BUDGET_U128 {
            Some(Q {
                num: n as i64,
                den: d as i64,
            })
        } else {
            None
        }
    }

    /// Exact decimal literal: `from_decimal(85, 2) == 0.85 == 17/20`. Returns
    /// `None` if `10^dec_places` overflows or the reduced value exceeds the
    /// budget. This is the engine's primary ingestion path for short-decimal
    /// reliabilities / competences / weights.
    #[inline]
    pub fn from_decimal(mantissa: i64, dec_places: u8) -> Option<Q> {
        let mut den: i128 = 1;
        let mut i = 0u8;
        while i < dec_places {
            den = den.checked_mul(10)?;
            i += 1;
        }
        let (n, d) = reduce_i128(mantissa as i128, den);
        if n.unsigned_abs() <= BUDGET_U128 && (d as u128) <= BUDGET_U128 {
            Some(Q {
                num: n as i64,
                den: d as i64,
            })
        } else {
            None
        }
    }

    /// Convert an `f64` to a `Q` with the directed inequality of `dir` against
    /// the exact real value of `v`, and error `≤ 2^-60 · max(1, |v|)`.
    ///
    /// Returns `None` on NaN, ±∞, or `|v| > 2^61` (the accepted restriction).
    /// Implemented by exact bit decomposition of the IEEE-754 value
    /// (`v = ± mantissa · 2^exp`) followed by [`round_to_budget`], so it touches
    /// **no** floating-point arithmetic and is inside the verified region — it
    /// is *not* a trusted boundary (see `TRUSTED.md`).
    pub fn from_f64_dir(v: f64, dir: Dir) -> Option<Q> {
        if !v.is_finite() {
            return None;
        }
        if v == 0.0 {
            return Some(Q::zero());
        }
        // Restriction |v| ≤ 2^61 keeps the integer-part shift within i128.
        if v.abs() > (1u64 << 61) as f64 {
            return None;
        }
        let bits_ = v.to_bits();
        let sign_neg = (bits_ >> 63) == 1;
        let exp_field = ((bits_ >> 52) & 0x7ff) as i64;
        let frac = (bits_ & 0x000f_ffff_ffff_ffff) as u128; // low 52 bits
        let (mantissa, exp): (u128, i64) = if exp_field == 0 {
            (frac, -1074) // subnormal: value = frac · 2^-1074
        } else {
            ((1u128 << 52) | frac, exp_field - 1075) // normal
        };
        Some(from_dyadic(sign_neg, mantissa, exp, dir))
    }
}

/// Round the exact dyadic value `± mantissa · 2^exp` (`mantissa ≥ 0`) into a
/// canonical [`Q`] under direction `dir`. Used only by [`Q::from_f64_dir`];
/// integer-only, no float reasoning.
fn from_dyadic(sign_neg: bool, m: u128, exp: i64, dir: Dir) -> Q {
    if m == 0 {
        return Q::zero();
    }
    if exp >= 0 {
        // Caller guaranteed |v| ≤ 2^61, so m << exp fits i128.
        let num = (m << (exp as u32)) as i128;
        let n = if sign_neg { -num } else { num };
        return round_to_budget(n, 1, dir);
    }
    let k = (-exp) as u32;
    if k <= 61 {
        // Exact dyadic: den = 2^k ≤ 2^61 ≤ BUDGET, |m| ≤ 2^53 ≤ BUDGET.
        let num = m as i128;
        let n = if sign_neg { -num } else { num };
        return round_to_budget(n, 1i128 << k, dir);
    }
    // k > 61: snap to the grid den = 2^61.
    let drop = k - 61;
    let (q, rem) = if drop >= 128 {
        (0u128, m)
    } else {
        (m >> drop, m - ((m >> drop) << drop))
    };
    let has_rem = rem != 0;
    let p: u128 = match dir {
        Dir::Down => {
            if sign_neg {
                if has_rem {
                    q + 1
                } else {
                    q
                }
            } else {
                q
            }
        }
        Dir::Up => {
            if sign_neg {
                q
            } else if has_rem {
                q + 1
            } else {
                q
            }
        }
        Dir::Nearest => {
            let up = if (1..128).contains(&drop) {
                let half = 1u128 << (drop - 1);
                rem >= half && has_rem
            } else {
                false
            };
            if up {
                q + 1
            } else {
                q
            }
        }
    };
    let num_signed = if sign_neg { -(p as i128) } else { p as i128 };
    round_to_budget(num_signed, 1i128 << 61, dir)
}

// ---------------------------------------------------------------------------
// Arithmetic (§2.2)
// ---------------------------------------------------------------------------

impl Q {
    /// `self + other`, rounded to the budget with `Dir::Nearest` (exact when the
    /// result fits, per R1). Every `i128` intermediate is in range (V2).
    #[inline]
    pub fn add(self, other: Q) -> Q {
        self.add_dir(other, Dir::Nearest)
    }

    /// `self + other` with an explicit rounding direction (for a future interval
    /// layer). Numerator `a.num·b.den + b.num·a.den` is `≤ 2·(2^62)^2 < 2^125`;
    /// denominator `a.den·b.den < 2^124`.
    #[inline]
    pub fn add_dir(self, other: Q, dir: Dir) -> Q {
        let n = self.num as i128 * other.den as i128 + other.num as i128 * self.den as i128;
        let d = self.den as i128 * other.den as i128;
        round_to_budget(n, d, dir)
    }

    /// `self − other`, rounded with `Dir::Nearest`.
    #[inline]
    pub fn sub(self, other: Q) -> Q {
        self.sub_dir(other, Dir::Nearest)
    }

    /// `self − other` with an explicit rounding direction.
    #[inline]
    pub fn sub_dir(self, other: Q, dir: Dir) -> Q {
        let n = self.num as i128 * other.den as i128 - other.num as i128 * self.den as i128;
        let d = self.den as i128 * other.den as i128;
        round_to_budget(n, d, dir)
    }

    /// `self · other`, rounded with `Dir::Nearest`. Numerator/denominator each
    /// `≤ (2^62)^2 < 2^124`.
    #[inline]
    pub fn mul(self, other: Q) -> Q {
        self.mul_dir(other, Dir::Nearest)
    }

    /// `self · other` with an explicit rounding direction.
    #[inline]
    pub fn mul_dir(self, other: Q, dir: Dir) -> Q {
        let n = self.num as i128 * other.num as i128;
        let d = self.den as i128 * other.den as i128;
        round_to_budget(n, d, dir)
    }

    /// `self / other`, rounded with `Dir::Nearest`.
    ///
    /// # Panics
    /// Panics if `other.is_zero()`. Division by zero is a **precondition**
    /// (statically discharged by the caller under Verus), never a silent result.
    #[inline]
    pub fn div(self, other: Q) -> Q {
        self.div_dir(other, Dir::Nearest)
    }

    /// `self / other` with an explicit rounding direction. Panics if
    /// `other.is_zero()` (see [`Q::div`]).
    #[inline]
    pub fn div_dir(self, other: Q, dir: Dir) -> Q {
        assert!(!other.is_zero(), "Q::div by zero (precondition violated)");
        let n = self.num as i128 * other.den as i128;
        let d = self.den as i128 * other.num as i128;
        round_to_budget(n, d, dir)
    }

    /// `checked` division: `None` iff `other.is_zero()`. Convenience for callers
    /// that cannot statically discharge the non-zero precondition.
    #[inline]
    pub fn checked_div(self, other: Q) -> Option<Q> {
        if other.is_zero() {
            None
        } else {
            Some(self.div_dir(other, Dir::Nearest))
        }
    }

    /// Negation — always exact (I2 is symmetric in sign; `|num| ≤ 2^62 − 1`
    /// negates without overflow).
    #[inline]
    pub fn neg(self) -> Q {
        Q {
            num: -self.num,
            den: self.den,
        }
    }

    /// Absolute value — always exact.
    #[inline]
    pub fn abs(self) -> Q {
        Q {
            num: self.num.abs(),
            den: self.den,
        }
    }

    /// Reciprocal `den / num` — always exact (swaps and re-signs).
    ///
    /// # Panics
    /// Panics if `self.is_zero()` (precondition, like [`Q::div`]).
    #[inline]
    pub fn recip(self) -> Q {
        assert!(!self.is_zero(), "Q::recip of zero (precondition violated)");
        if self.num < 0 {
            Q {
                num: -self.den,
                den: -self.num,
            }
        } else {
            Q {
                num: self.den,
                den: self.num,
            }
        }
    }

    /// Minimum (exact).
    #[inline]
    pub fn min(self, other: Q) -> Q {
        if self.le(other) {
            self
        } else {
            other
        }
    }

    /// Maximum (exact).
    #[inline]
    pub fn max(self, other: Q) -> Q {
        if self.le(other) {
            other
        } else {
            self
        }
    }

    /// Clamp to `[lo, hi]` (exact).
    ///
    /// # Panics
    /// Panics if `lo > hi` (precondition).
    #[inline]
    #[allow(clippy::manual_clamp)] // uses the exact Q order + explicit precondition assert
    pub fn clamp(self, lo: Q, hi: Q) -> Q {
        assert!(lo.le(hi), "Q::clamp requires lo <= hi");
        if self.lt(lo) {
            lo
        } else if self.gt(hi) {
            hi
        } else {
            self
        }
    }
}

// ---------------------------------------------------------------------------
// Comparison and predicates (§2.3) — all exact, total.
// ---------------------------------------------------------------------------

impl Q {
    /// Exact equality (identical canonical form).
    #[inline]
    pub fn eq(self, other: Q) -> bool {
        self.num == other.num && self.den == other.den
    }

    /// Exact `<` via cross-multiplication (`den > 0` for both, no overflow).
    #[inline]
    pub fn lt(self, other: Q) -> bool {
        (self.num as i128 * other.den as i128) < (other.num as i128 * self.den as i128)
    }

    /// Exact `≤`.
    #[inline]
    pub fn le(self, other: Q) -> bool {
        (self.num as i128 * other.den as i128) <= (other.num as i128 * self.den as i128)
    }

    /// Exact `>`.
    #[inline]
    pub fn gt(self, other: Q) -> bool {
        other.lt(self)
    }

    /// Exact `≥`.
    #[inline]
    pub fn ge(self, other: Q) -> bool {
        other.le(self)
    }

    /// Total ordering agreeing with the mathematical order.
    #[inline]
    pub fn cmp_q(self, other: Q) -> Ordering {
        let lhs = self.num as i128 * other.den as i128;
        let rhs = other.num as i128 * self.den as i128;
        lhs.cmp(&rhs)
    }

    /// Is this exactly `0`?
    #[inline]
    pub fn is_zero(self) -> bool {
        self.num == 0
    }

    /// Is this exactly `1`?
    #[inline]
    pub fn is_one(self) -> bool {
        self.num == 1 && self.den == 1
    }

    /// Sign: `-1`, `0`, or `1`.
    #[inline]
    pub fn signum(self) -> i32 {
        match self.num.cmp(&0) {
            Ordering::Less => -1,
            Ordering::Equal => 0,
            Ordering::Greater => 1,
        }
    }

    /// Is `0 ≤ self ≤ 1`? (The engine checks this constantly on belief masses.)
    #[inline]
    pub fn in_unit_interval(self) -> bool {
        (0..=self.den).contains(&self.num)
    }

    /// The stored numerator (canonical).
    #[inline]
    pub const fn numer(self) -> i64 {
        self.num
    }

    /// The stored denominator (canonical, `> 0`).
    #[inline]
    pub const fn denom(self) -> i64 {
        self.den
    }
}

// ---------------------------------------------------------------------------
// Conversions out and plumbing (§2.4)
// ---------------------------------------------------------------------------

impl Q {
    /// Convert to `f64` for **display / DTO boundary only**. This is the one
    /// documented trusted float boundary (`TRUSTED.md`); the result must never
    /// be fed back into `Q` arithmetic.
    #[inline]
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

impl PartialOrd for Q {
    #[inline]
    fn partial_cmp(&self, other: &Q) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Q {
    #[inline]
    fn cmp(&self, other: &Q) -> Ordering {
        self.cmp_q(*other)
    }
}

impl Default for Q {
    #[inline]
    fn default() -> Q {
        Q::zero()
    }
}

// ---------------------------------------------------------------------------
// Operator sugar (Nearest rounding) — convenience over the named methods.
// ---------------------------------------------------------------------------

impl core::ops::Add for Q {
    type Output = Q;
    #[inline]
    fn add(self, rhs: Q) -> Q {
        Q::add(self, rhs)
    }
}
impl core::ops::Sub for Q {
    type Output = Q;
    #[inline]
    fn sub(self, rhs: Q) -> Q {
        Q::sub(self, rhs)
    }
}
impl core::ops::Mul for Q {
    type Output = Q;
    #[inline]
    fn mul(self, rhs: Q) -> Q {
        Q::mul(self, rhs)
    }
}
impl core::ops::Div for Q {
    type Output = Q;
    #[inline]
    fn div(self, rhs: Q) -> Q {
        Q::div(self, rhs)
    }
}
impl core::ops::Neg for Q {
    type Output = Q;
    #[inline]
    fn neg(self) -> Q {
        Q::neg(self)
    }
}

// ---------------------------------------------------------------------------
// n-ary helpers (§2.5) — defined as fixed-order binary folds.
// ---------------------------------------------------------------------------

/// Left-to-right sum. Fixed evaluation order ⟹ deterministic; accumulated error
/// `≤ k · 2^-60` after `k` addends (V8).
pub fn sum(xs: &[Q]) -> Q {
    let mut acc = Q::zero();
    for &x in xs {
        acc = acc.add(x);
    }
    acc
}

/// Left-to-right product. Fixed evaluation order; accumulated error `≤ k · 2^-60`.
pub fn product(xs: &[Q]) -> Q {
    let mut acc = Q::one();
    for &x in xs {
        acc = acc.mul(x);
    }
    acc
}

/// Weighted mean `Σ wᵢ·xᵢ / Σ wᵢ` over `(weight, value)` pairs (the ABF formula
/// shape). Returns `None` if the pairs are empty or the weights sum to zero.
pub fn weighted_mean(pairs: &[(Q, Q)]) -> Option<Q> {
    if pairs.is_empty() {
        return None;
    }
    let mut wsum = Q::zero();
    let mut acc = Q::zero();
    for &(w, x) in pairs {
        wsum = wsum.add(w);
        acc = acc.add(w.mul(x));
    }
    acc.checked_div(wsum)
}

// ---------------------------------------------------------------------------
// serde (feature-gated) — serialize as the (num, den) integer pair for exact
// round-trip, unlike any f64 encoding.
// ---------------------------------------------------------------------------

#[cfg(feature = "serde")]
mod serde_impl {
    use super::Q;
    use serde::{Deserialize, Deserializer, Serialize, Serializer};

    #[derive(Serialize, Deserialize)]
    struct QRepr {
        num: i64,
        den: i64,
    }

    impl Serialize for Q {
        fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
            QRepr {
                num: self.numer(),
                den: self.denom(),
            }
            .serialize(s)
        }
    }

    impl<'de> Deserialize<'de> for Q {
        fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Q, D::Error> {
            let r = QRepr::deserialize(d)?;
            // Re-validate the invariants on ingest — a hostile or corrupt encoding
            // must not be able to construct a non-canonical / out-of-budget Q.
            Q::new(r.num, r.den).ok_or_else(|| serde::de::Error::custom("invalid Q (num/den)"))
        }
    }
}

#[cfg(test)]
mod unit_tests;
