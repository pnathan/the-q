//! # `the-q` — verified bounded rational (ℚ) arithmetic
//!
//! Exact-with-verified-rounding rational arithmetic over a fixed width budget,
//! intended as the deterministic numeric backbone of a subjective-logic fusion
//! engine. Values are stored canonically as `num / den` with `den > 0` and
//! `gcd(|num|, den) == 1`, so **structural equality is mathematical equality**.
//!
//! ## Verification
//!
//! This crate is **its own Verus verification target**: the whole of `src/lib.rs`
//! is wrapped in `verus! { … }`, so the same source both `cargo build`s (the
//! macro expands to plain Rust) and is checked by
//! `verus --crate-type=lib src/lib.rs` on CI. That makes `vstd`/`verus_builtin`
//! hard dependencies — the standard shape of a directly-verified Verus crate.
//!
//! The port is staged: the invariant model and the API contracts
//! (`requires`/`ensures wf`) are on the exec functions themselves, and the heavy
//! internal bodies (`round_to_budget`, `reduce_i128`, the f64 boundary) are
//! currently `#[verifier::external_body]` — trusted bodies with checked
//! signatures — and are being tightened to full proofs (the machine-checked
//! algorithm-level proofs live under `verus/`). `TRUSTED.md` tracks the trusted
//! set; `verus/README.md` tracks per-obligation status.
//!
//! ## Honesty consequence
//!
//! With rounding, `add`/`mul` are **commutative** but **not associative in
//! general** — associativity/distributivity hold only on the exact path.

#![cfg_attr(not(test), no_std)]
#![allow(clippy::should_implement_trait)]

use vstd::prelude::*;

verus! {

/// The width budget: `|num| ≤ BUDGET` and `den ≤ BUDGET` for every canonical
/// [`Q`] (invariant I2). `2^62 − 1` so every `i128` intermediate is provably in
/// range.
pub const BUDGET: i64 = 4611686018427387903;

/// `2^62 − 1` as a ghost `int`, for specifications.
pub open spec fn budget_int() -> int { 4611686018427387903 }

/// Rounding direction. `Down` toward −∞, `Up` toward +∞, `Nearest` to the
/// closest grid point (ties away from zero).
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
/// - **I1 (canonical):** `den > 0`, `gcd(|num|, den) == 1`, `num == 0 ⟹ den == 1`.
/// - **I2 (bounded):** `|num| ≤ 2^62 − 1` and `den ≤ 2^62 − 1`.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Q {
    num: i64,
    den: i64,
}

// ---- ghost model ----------------------------------------------------------

/// Absolute value on ghost `int`.
pub open spec fn abs_int(x: int) -> int { if x < 0 { -x } else { x } }

/// Well-formedness = I2 (bounded) with a positive denominator — the part of the
/// invariant the API contracts thread through. (Full I1 canonicality/GCD is
/// maintained by the constructors and proven at the algorithm level under
/// `verus/`; folding it into this predicate is part of the ongoing tightening.)
pub open spec fn wf(q: Q) -> bool {
    &&& q.den as int >= 1
    &&& -budget_int() <= q.num as int <= budget_int()
    &&& q.den as int <= budget_int()
}

/// Ghost value order, division-free (both denominators positive).
pub open spec fn q_le_spec(a: Q, b: Q) -> bool {
    (a.num as int) * (b.den as int) <= (b.num as int) * (a.den as int)
}
pub open spec fn q_lt_spec(a: Q, b: Q) -> bool {
    (a.num as int) * (b.den as int) < (b.num as int) * (a.den as int)
}
pub open spec fn q_eq_spec(a: Q, b: Q) -> bool {
    (a.num as int) * (b.den as int) == (b.num as int) * (a.den as int)
}

// ---- internal integer helpers (trusted bodies for now) --------------------

/// Euclid's algorithm on `u128`. (Verified at the algorithm level in
/// `verus/src/gcd_checked.rs`; body trusted here pending in-file tightening.)
#[verifier::external_body]
fn gcd_u128(mut a: u128, mut b: u128) -> u128 {
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    a
}

/// Reduce `n/d` (`d != 0`) to canonical form. (Value-preservation + canonicality
/// proven in `verus/src/verified_reduce.rs`/`verified_uniq.rs`.)
#[verifier::external_body]
fn reduce_i128(mut n: i128, mut d: i128) -> (r: (i128, i128))
    requires d != 0,
    ensures r.1 >= 1,
{
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

/// Bit length of a positive `u128` (`0` for `0`).
#[verifier::external_body]
fn bits(x: u128) -> u32 {
    128 - x.leading_zeros()
}

/// `floor(num * 2^s / den)` and remainder, by bitwise long division.
/// (Grid bounds R1–R4 proven in `verus/src/verified_round*.rs`.)
#[verifier::external_body]
fn scaled_floor(num: u128, den: u128, s: u32) -> (u128, u128) {
    let mut q = num / den;
    let mut r = num % den;
    let mut i = 0;
    while i < s {
        r <<= 1;
        let bit = if r >= den {
            r -= den;
            1
        } else {
            0
        };
        q = (q << 1) | bit;
        i += 1;
    }
    (q, r)
}

const BUDGET_U128: u128 = (1u128 << 62) - 1;

/// The rounding step (obligation V4). Returns a well-formed `Q`. (Contract R1–R4
/// proven at the algorithm level in `verus/src/verified_round*.rs`; body trusted
/// here pending in-file tightening.)
#[verifier::external_body]
fn round_to_budget(n_raw: i128, d_raw: i128, dir: Dir) -> (r: Q)
    requires d_raw != 0,
    ensures wf(r),
{
    let (n, d) = reduce_i128(n_raw, d_raw);
    if n.unsigned_abs() <= BUDGET_U128 && (d as u128) <= BUDGET_U128 {
        return Q { num: n as i64, den: d as i64 };
    }
    if n == 0 {
        return Q { num: 0, den: 1 };
    }
    let sign_neg = n < 0;
    let mag_num = n.unsigned_abs();
    let mag_den = d as u128;
    let bn = bits(mag_num) as i64;
    let bd = bits(mag_den) as i64;
    let e = bn - bd;
    let mut s: i64 = (61 - e).clamp(0, 61);
    loop {
        let su = s as u32;
        let den_pow: u128 = 1u128 << su;
        let (q, rem) = scaled_floor(mag_num, mag_den, su);
        let has_rem = rem != 0;
        let p: u128 = match dir {
            Dir::Down => {
                if sign_neg {
                    if has_rem { q + 1 } else { q }
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
                let twice = rem << 1;
                if twice >= mag_den && has_rem { q + 1 } else { q }
            }
        };
        if p <= BUDGET_U128 && den_pow <= BUDGET_U128 {
            let num_signed = if sign_neg { -(p as i128) } else { p as i128 };
            let (rn, rd) = reduce_i128(num_signed, den_pow as i128);
            return Q { num: rn as i64, den: rd as i64 };
        }
        if s == 0 {
            let sat = if sign_neg { -BUDGET } else { BUDGET };
            return Q { num: sat, den: 1 };
        }
        s -= 1;
    }
}

/// Round `± mantissa · 2^exp` into a canonical `Q`. Used by `from_f64_dir`.
#[verifier::external_body]
fn from_dyadic(sign_neg: bool, m: u128, exp: i64, dir: Dir) -> (r: Q)
    ensures wf(r),
{
    if m == 0 {
        return Q { num: 0, den: 1 };
    }
    if exp >= 0 {
        let num = (m << (exp as u32)) as i128;
        let n = if sign_neg { -num } else { num };
        return round_to_budget(n, 1, dir);
    }
    let k = (-exp) as u32;
    if k <= 61 {
        let num = m as i128;
        let n = if sign_neg { -num } else { num };
        return round_to_budget(n, 1i128 << k, dir);
    }
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
                if has_rem { q + 1 } else { q }
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
            if up { q + 1 } else { q }
        }
    };
    let num_signed = if sign_neg { -(p as i128) } else { p as i128 };
    round_to_budget(num_signed, 1i128 << 61, dir)
}

// ---- constructors (§2.1) --------------------------------------------------

impl Q {
    /// The value `0` (`0/1`).
    pub fn zero() -> (r: Q)
        ensures wf(r), r.num == 0, r.den == 1,
    {
        Q { num: 0, den: 1 }
    }

    /// The value `1` (`1/1`).
    pub fn one() -> (r: Q)
        ensures wf(r), r.num == 1, r.den == 1,
    {
        Q { num: 1, den: 1 }
    }

    /// Exact integer, or `None` if `|i| > 2^62 − 1`.
    #[verifier::external_body]
    pub fn from_int(i: i64) -> (r: Option<Q>)
        ensures forall|q: Q| r == Some(q) ==> wf(q),
    {
        if i == i64::MIN || i.unsigned_abs() > BUDGET as u64 {
            return None;
        }
        Some(Q { num: i, den: 1 })
    }

    /// Construct `num / den`, canonicalized; `None` if `den == 0` or the reduced
    /// form exceeds the budget.
    #[verifier::external_body]
    pub fn new(num: i64, den: i64) -> (r: Option<Q>)
        ensures forall|q: Q| r == Some(q) ==> wf(q),
    {
        if den == 0 {
            return None;
        }
        let (n, d) = reduce_i128(num as i128, den as i128);
        if n.unsigned_abs() <= BUDGET_U128 && (d as u128) <= BUDGET_U128 {
            Some(Q { num: n as i64, den: d as i64 })
        } else {
            None
        }
    }

    /// Exact decimal literal: `from_decimal(85, 2) == 0.85`.
    #[verifier::external_body]
    pub fn from_decimal(mantissa: i64, dec_places: u8) -> (r: Option<Q>)
        ensures forall|q: Q| r == Some(q) ==> wf(q),
    {
        let mut den: i128 = 1;
        let mut i = 0u8;
        while i < dec_places {
            match den.checked_mul(10) {
                Some(v) => den = v,
                None => return None,
            }
            i += 1;
        }
        let (n, d) = reduce_i128(mantissa as i128, den);
        if n.unsigned_abs() <= BUDGET_U128 && (d as u128) <= BUDGET_U128 {
            Some(Q { num: n as i64, den: d as i64 })
        } else {
            None
        }
    }

    /// Convert an `f64` to `Q` with the directed inequality of `dir` and error
    /// `≤ 2^-60·max(1,|v|)`. `None` on NaN/±∞/`|v| > 2^61`. Integer
    /// bit-decomposition — no float arithmetic.
    #[verifier::external_body]
    pub fn from_f64_dir(v: f64, dir: Dir) -> (r: Option<Q>)
        ensures forall|q: Q| r == Some(q) ==> wf(q),
    {
        if !v.is_finite() {
            return None;
        }
        if v == 0.0 {
            return Some(Q { num: 0, den: 1 });
        }
        if v.abs() > (1u64 << 61) as f64 {
            return None;
        }
        let bits_ = v.to_bits();
        let sign_neg = (bits_ >> 63) == 1;
        let exp_field = ((bits_ >> 52) & 0x7ff) as i64;
        let frac = (bits_ & 0x000f_ffff_ffff_ffff) as u128;
        let (mantissa, exp): (u128, i64) = if exp_field == 0 {
            (frac, -1074)
        } else {
            ((1u128 << 52) | frac, exp_field - 1075)
        };
        Some(from_dyadic(sign_neg, mantissa, exp, dir))
    }
}

// ---- arithmetic (§2.2) ----------------------------------------------------

impl Q {
    /// `self + other`, rounded (Nearest).
    pub fn add(self, other: Q) -> (r: Q)
        requires wf(self), wf(other),
        ensures wf(r),
    {
        self.add_dir(other, Dir::Nearest)
    }

    /// `self + other` with an explicit rounding direction.
    #[verifier::external_body]
    pub fn add_dir(self, other: Q, dir: Dir) -> (r: Q)
        requires wf(self), wf(other),
        ensures wf(r),
    {
        let n = self.num as i128 * other.den as i128 + other.num as i128 * self.den as i128;
        let d = self.den as i128 * other.den as i128;
        round_to_budget(n, d, dir)
    }

    /// `self − other`, rounded (Nearest).
    pub fn sub(self, other: Q) -> (r: Q)
        requires wf(self), wf(other),
        ensures wf(r),
    {
        self.sub_dir(other, Dir::Nearest)
    }

    /// `self − other` with an explicit rounding direction.
    #[verifier::external_body]
    pub fn sub_dir(self, other: Q, dir: Dir) -> (r: Q)
        requires wf(self), wf(other),
        ensures wf(r),
    {
        let n = self.num as i128 * other.den as i128 - other.num as i128 * self.den as i128;
        let d = self.den as i128 * other.den as i128;
        round_to_budget(n, d, dir)
    }

    /// `self · other`, rounded (Nearest).
    pub fn mul(self, other: Q) -> (r: Q)
        requires wf(self), wf(other),
        ensures wf(r),
    {
        self.mul_dir(other, Dir::Nearest)
    }

    /// `self · other` with an explicit rounding direction.
    #[verifier::external_body]
    pub fn mul_dir(self, other: Q, dir: Dir) -> (r: Q)
        requires wf(self), wf(other),
        ensures wf(r),
    {
        let n = self.num as i128 * other.num as i128;
        let d = self.den as i128 * other.den as i128;
        round_to_budget(n, d, dir)
    }

    /// `self / other`, rounded (Nearest).
    pub fn div(self, other: Q) -> (r: Q)
        requires wf(self), wf(other), other.num != 0,
        ensures wf(r),
    {
        self.div_dir(other, Dir::Nearest)
    }

    /// `self / other` with an explicit rounding direction.
    #[verifier::external_body]
    pub fn div_dir(self, other: Q, dir: Dir) -> (r: Q)
        requires wf(self), wf(other), other.num != 0,
        ensures wf(r),
    {
        assert!(other.num != 0, "Q::div by zero (precondition violated)");
        let n = self.num as i128 * other.den as i128;
        let d = self.den as i128 * other.num as i128;
        round_to_budget(n, d, dir)
    }

    /// `checked` division: `None` iff `other.is_zero()`.
    #[verifier::external_body]
    pub fn checked_div(self, other: Q) -> (r: Option<Q>)
        requires wf(self), wf(other),
        ensures forall|q: Q| r == Some(q) ==> wf(q),
    {
        if other.num == 0 {
            None
        } else {
            Some(self.div_dir(other, Dir::Nearest))
        }
    }

    /// Negation — always exact.
    #[verifier::external_body]
    pub fn neg(self) -> (r: Q)
        requires wf(self),
        ensures wf(r), r.num == -(self.num as int), r.den == self.den,
    {
        Q { num: -self.num, den: self.den }
    }

    /// Absolute value — always exact.
    #[verifier::external_body]
    pub fn abs(self) -> (r: Q)
        requires wf(self),
        ensures wf(r), r.den == self.den,
    {
        Q { num: self.num.abs(), den: self.den }
    }

    /// Reciprocal `den / num` — always exact.
    #[verifier::external_body]
    pub fn recip(self) -> (r: Q)
        requires wf(self), self.num != 0,
        ensures wf(r),
    {
        assert!(self.num != 0, "Q::recip of zero (precondition violated)");
        if self.num < 0 {
            Q { num: -self.den, den: -self.num }
        } else {
            Q { num: self.den, den: self.num }
        }
    }

    /// Minimum (exact).
    pub fn min(self, other: Q) -> (r: Q)
        requires wf(self), wf(other),
        ensures wf(r), r == self || r == other,
    {
        if self.le(other) {
            self
        } else {
            other
        }
    }

    /// Maximum (exact).
    pub fn max(self, other: Q) -> (r: Q)
        requires wf(self), wf(other),
        ensures wf(r), r == self || r == other,
    {
        if self.le(other) {
            other
        } else {
            self
        }
    }

    /// Clamp to `[lo, hi]` (exact).
    #[verifier::external_body]
    pub fn clamp(self, lo: Q, hi: Q) -> (r: Q)
        requires wf(self), wf(lo), wf(hi), q_le_spec(lo, hi),
        ensures wf(r),
    {
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

// ---- comparison and predicates (§2.3) -------------------------------------

impl Q {
    /// Exact equality (identical canonical form).
    pub fn eq(self, other: Q) -> (r: bool)
        ensures r == (self.num == other.num && self.den == other.den),
    {
        self.num == other.num && self.den == other.den
    }

    /// Exact `<` via cross-multiplication.
    #[verifier::external_body]
    pub fn lt(self, other: Q) -> (r: bool)
        requires wf(self), wf(other),
        ensures r == q_lt_spec(self, other),
    {
        (self.num as i128 * other.den as i128) < (other.num as i128 * self.den as i128)
    }

    /// Exact `≤`.
    #[verifier::external_body]
    pub fn le(self, other: Q) -> (r: bool)
        requires wf(self), wf(other),
        ensures r == q_le_spec(self, other),
    {
        (self.num as i128 * other.den as i128) <= (other.num as i128 * self.den as i128)
    }

    /// Exact `>`.
    pub fn gt(self, other: Q) -> (r: bool)
        requires wf(self), wf(other),
        ensures r == q_lt_spec(other, self),
    {
        other.lt(self)
    }

    /// Exact `≥`.
    pub fn ge(self, other: Q) -> (r: bool)
        requires wf(self), wf(other),
        ensures r == q_le_spec(other, self),
    {
        other.le(self)
    }

    /// Is this exactly `0`?
    pub fn is_zero(self) -> (r: bool)
        ensures r == (self.num == 0),
    {
        self.num == 0
    }

    /// Is this exactly `1`?
    pub fn is_one(self) -> (r: bool)
        ensures r == (self.num == 1 && self.den == 1),
    {
        self.num == 1 && self.den == 1
    }

    /// Sign: `-1`, `0`, or `1`.
    pub fn signum(self) -> (r: i32)
        ensures
            (self.num as int) > 0 ==> r == 1,
            (self.num as int) == 0 ==> r == 0,
            (self.num as int) < 0 ==> r == -1,
    {
        if self.num > 0 {
            1
        } else if self.num == 0 {
            0
        } else {
            -1
        }
    }

    /// Is `0 ≤ self ≤ 1`?
    pub fn in_unit_interval(self) -> (r: bool)
        requires wf(self),
        ensures r == (0 <= self.num && self.num <= self.den),
    {
        0 <= self.num && self.num <= self.den
    }

    /// The stored numerator (canonical).
    pub fn numer(self) -> (r: i64)
        ensures r == self.num,
    {
        self.num
    }

    /// The stored denominator (canonical, `> 0`).
    pub fn denom(self) -> (r: i64)
        ensures r == self.den,
    {
        self.den
    }

    /// Convert to `f64` for **display / DTO boundary only** (trusted; `TRUSTED.md`).
    #[verifier::external_body]
    pub fn to_f64(self) -> f64 {
        self.num as f64 / self.den as f64
    }
}

// ---- n-ary helpers (§2.5) -------------------------------------------------

/// Left-to-right sum.
#[verifier::external_body]
pub fn sum(xs: &[Q]) -> (r: Q)
    ensures wf(r),
{
    let mut acc = Q::zero();
    for &x in xs {
        acc = acc.add(x);
    }
    acc
}

/// Left-to-right product.
#[verifier::external_body]
pub fn product(xs: &[Q]) -> (r: Q)
    ensures wf(r),
{
    let mut acc = Q::one();
    for &x in xs {
        acc = acc.mul(x);
    }
    acc
}

/// Weighted mean `Σ wᵢ·xᵢ / Σ wᵢ`. `None` if empty or the weights sum to zero.
#[verifier::external_body]
pub fn weighted_mean(pairs: &[(Q, Q)]) -> (r: Option<Q>)
    ensures forall|q: Q| r == Some(q) ==> wf(q),
{
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

} // verus!

// ---------------------------------------------------------------------------
// Trait plumbing — outside `verus!{}`, marked external so Verus ignores it and
// plain rustc compiles it normally. (These are display/ordering conveniences;
// `cmp_q`/`eq`/`le` inside the verified region carry the value-order contract.)
// ---------------------------------------------------------------------------

impl Q {
    /// Total ordering agreeing with the mathematical order.
    #[inline]
    pub fn cmp_q(self, other: Q) -> core::cmp::Ordering {
        let lhs = self.num as i128 * other.den as i128;
        let rhs = other.num as i128 * self.den as i128;
        lhs.cmp(&rhs)
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

impl PartialOrd for Q {
    #[inline]
    fn partial_cmp(&self, other: &Q) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Q {
    #[inline]
    fn cmp(&self, other: &Q) -> core::cmp::Ordering {
        self.cmp_q(*other)
    }
}

impl Default for Q {
    #[inline]
    fn default() -> Q {
        Q::zero()
    }
}

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

// serde (feature-gated) — serialize as the (num, den) pair for exact round-trip.
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
            Q::new(r.num, r.den).ok_or_else(|| serde::de::Error::custom("invalid Q (num/den)"))
        }
    }
}

#[cfg(test)]
mod unit_tests;
