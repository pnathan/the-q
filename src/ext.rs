//! The extended `Q`: a rational, or an explicit non-representable state.
//!
//! This module is an extension layer over the proven kernel. It is not a
//! rewrite of the kernel. [`Rat`] keeps its invariant, thus each obligation
//! about `Rat` keeps its statement. This module adds a discriminant. The
//! discriminant makes the condition "not a representable rational" an
//! observable state, and not a condition that the caller must rule out.
//!
//! Issue #26 holds the design. Two points from that design apply here:
//!
//! * A special value carries no `num` or `den`. No operation can thus read a
//!   special value as a number. This encoding removes the `recip(0)` class of
//!   defect. The discriminant also makes an omitted case a compile error. A
//!   sentinel `den == 0` encoding does not.
//! * There is no `is_finite()`. `PosSat` denotes finite reals, because a
//!   magnitude above the budget is still a real number. "Finite" is thus the
//!   wrong axis for this type. The four predicates below use the axis that
//!   exists.

use verus_builtin_macros::verus;

#[allow(unused_imports)]
use verus_builtin::*;
#[allow(unused_imports)]
use vstd::prelude::*;

use crate::types::{Dir, Rat};

verus! {

/// The sign of a value that has one.
///
/// [`Q::signum`] returns `Option<Sign>` and not an integer, because
/// `signum(Nan)` has no answer. `Nan` denotes all of `ℝ ∪ {±∞}`, thus no sign
/// is sound. `None` is the `Nan` case only. Each other state has a definite
/// sign, including both saturations and both infinities.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Sign {
    /// Strictly less than zero.
    Negative,
    /// Exactly zero.
    Zero,
    /// Strictly greater than zero.
    Positive,
}

/// A bounded rational, or an explicit statement that the value is not one.
///
/// # The states
///
/// | variant | denotes |
/// |---|---|
/// | `Number(x)` | `{x}` |
/// | `PosSat` | `(MAX_MAG, +∞)` — **reals only**, open at `MAX_MAG` |
/// | `NegSat` | `(-∞, -MAX_MAG)` — reals only |
/// | `PosInf` | `{+∞}` |
/// | `NegInf` | `{-∞}` |
/// | `Nan` | `ℝ ∪ {±∞}` — no information |
///
/// The code forces the open endpoint. `magnitude_fits` in [`crate::model`] is
/// `|n| <= MAX_MAG · d`, thus saturation starts above `MAX_MAG`, and `MAX_MAG`
/// is representable as `MAX_MAG/1`.
///
/// `PosSat` and `NegSat` denote reals only, and never `±∞`. That property makes
/// `Number(0) · PosSat` exactly `Number(0)`, where `0 · ±∞` is `Nan`.
/// Saturation is thus better behaved than infinity, and the type keeps the two
/// as separate states.
///
/// # Equality
///
/// `PartialEq` is derived. `Rat` is canonical, thus its structural equality is
/// mathematical equality. The special values carry no payload, thus there are
/// no two distinct `Nan` values and `Nan == Nan` is true. That reflexivity
/// keeps `Eq` lawful, keeps `Hash` consistent with `Eq`, and keeps the `Ord`
/// order total. This is an intentional departure from IEEE 754, where
/// `NaN != NaN`.
///
/// `Ord` is not derived. See the `Ord` implementation. A derived order follows
/// the declaration order of the variants below, which is not the order on
/// values.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Q {
    /// A representable rational.
    Number(Rat),
    /// The true magnitude exceeds `MAX_MAG` and the value is positive.
    PosSat,
    /// The true magnitude exceeds `MAX_MAG` and the value is negative.
    NegSat,
    /// Exactly `+∞`.
    PosInf,
    /// Exactly `-∞`.
    NegInf,
    /// No information about the value.
    Nan,
}

impl Q {
    /// The type invariant: a `Number` payload must satisfy the kernel invariant,
    /// and the specials are unconditionally well-formed because they carry
    /// nothing that could be malformed.
    ///
    /// This is the enum-level counterpart of `Rat::wf`. It is intentionally
    /// weak, because a special value has no representation invariant.
    pub open spec fn wf(self) -> bool {
        match self {
            Q::Number(x) => x.wf(),
            _ => true,
        }
    }

    // -----------------------------------------------------------------------
    // Classification
    //
    // These four `ensures` clauses restate their own bodies. A discriminant
    // test has no content beyond the variant that it accepts, thus the
    // specification and the implementation are the same statement. The clauses
    // prove nothing. They exist so that a caller in verified code can reason
    // about the result.
    //
    // The predicates below (`is_zero`, `signum` and others) are different. They
    // have content, and they delegate to the verified kernel.
    // -----------------------------------------------------------------------

    /// Whether this is a representable rational.
    pub open spec fn spec_is_number(self) -> bool {
        match self {
            Q::Number(_) => true,
            _ => false,
        }
    }

    /// Whether this is a saturation state.
    pub open spec fn spec_is_saturated(self) -> bool {
        match self {
            Q::PosSat => true,
            Q::NegSat => true,
            _ => false,
        }
    }

    /// Whether this is an infinity.
    pub open spec fn spec_is_infinite(self) -> bool {
        match self {
            Q::PosInf => true,
            Q::NegInf => true,
            _ => false,
        }
    }

    /// Whether this is `Nan`.
    pub open spec fn spec_is_nan(self) -> bool {
        match self {
            Q::Nan => true,
            _ => false,
        }
    }

    /// Whether this is a representable rational.
    ///
    /// The four classification predicates are mutually exclusive and jointly
    /// exhaustive. See `theorem_classification_partitions`.
    pub fn is_number(self) -> (r: bool)
        ensures
            r == self.spec_is_number(),
    {
        matches!(self, Q::Number(_))
    }

    /// Whether the true magnitude is known to exceed `MAX_MAG`.
    ///
    /// This predicate is not the negation of `is_number`. It separates an
    /// overflow from a division by zero. That distinction is the purpose of the
    /// saturation states.
    pub fn is_saturated(self) -> (r: bool)
        ensures
            r == self.spec_is_saturated(),
    {
        matches!(self, Q::PosSat | Q::NegSat)
    }

    /// Whether this is exactly `±∞`.
    pub fn is_infinite(self) -> (r: bool)
        ensures
            r == self.spec_is_infinite(),
    {
        matches!(self, Q::PosInf | Q::NegInf)
    }

    /// Whether this carries no information about the value.
    pub fn is_nan(self) -> (r: bool)
        ensures
            r == self.spec_is_nan(),
    {
        matches!(self, Q::Nan)
    }

    // -----------------------------------------------------------------------
    // Constructors
    //
    // Each constructor establishes `wf`. A special value establishes `wf`
    // trivially. There is no malformed special value, thus these constructors
    // cannot fail and need no `Option`.
    // -----------------------------------------------------------------------

    /// Lift a kernel rational into the extended type.
    pub fn number(x: Rat) -> (r: Q)
        requires
            x.wf(),
        ensures
            r.wf(),
            r == Q::Number(x),
            r.spec_is_number(),
    {
        Q::Number(x)
    }

    /// `0`.
    pub fn zero() -> (r: Q)
        ensures
            r.wf(),
            r.spec_is_number(),
            r.spec_is_value(0, 1),
            r.spec_is_zero(),
    {
        Q::Number(Rat::zero())
    }

    /// `1`.
    pub fn one() -> (r: Q)
        ensures
            r.wf(),
            r.spec_is_number(),
            r.spec_is_value(1, 1),
            r.spec_is_one(),
    {
        Q::Number(Rat::one())
    }

    /// `-1`.
    pub fn neg_one() -> (r: Q)
        ensures
            r.wf(),
            r.spec_is_number(),
            r.spec_is_value(-1, 1),
    {
        Q::Number(Rat::neg_one())
    }

    /// The rational `num / den`, or the special that stands for it.
    ///
    /// This constructor is total, unlike [`Rat::new`]. `den == 0` is a value in
    /// the type and not an out-of-band failure. Issue #26 §4 applies the
    /// IEEE 754 convention: `x/0` takes the positive-side limit, as IEEE does
    /// for `+0`, and `0/0` carries no information.
    ///
    /// # Saturation applies to the value, not to the components
    ///
    /// `Rat::new` returns `None` for two different reasons. The value exceeds
    /// the budget, as in `i64::MAX / 1`. Or the reduced denominator exceeds the
    /// budget while the value is small, as in `1 / i64::MIN`, which is
    /// approximately `-1.08e-19`. Only the first reason is saturation. A
    /// `NegSat` result for the second reason claims `|value| > MAX_MAG` for a
    /// value in `(-1, 0)`, which is an unsound denotation.
    ///
    /// The test here is thus `magnitude_fits` from [`crate::model`], applied to
    /// the value. A pair that fits in magnitude but not in its components is
    /// rounded, and not saturated. R3 makes that result sound. Issue #26 §11
    /// makes the same decision when it rejects a `Tiny` state: underflow to
    /// zero is inside the rounding contract.
    ///
    /// Where [`Rat::new`] succeeds, this constructor returns the same value.
    /// Rounding a representable value returns it unchanged (R1).
    pub fn new(num: i64, den: i64) -> (r: Q)
        ensures
            r.wf(),
            // Division by zero, per #26 §4, applied uniformly.
            (den == 0 && num == 0) ==> r == Q::Nan,
            (den == 0 && num > 0) ==> r == Q::PosInf,
            (den == 0 && num < 0) ==> r == Q::NegInf,
            // Away from a zero denominator the result is never an infinity or a
            // `Nan`: a ratio of two integers is a real number, and the only
            // question is whether it fits.
            den != 0 ==> (!r.spec_is_nan() && !r.spec_is_infinite()),
            // Saturation happens exactly when the *value* leaves the budget...
            den != 0 ==> (r.spec_is_saturated() <==> !crate::model::magnitude_fits(
                crate::q::signed_den_num(num as int, den as int),
                crate::model::abs_int(den as int),
            )),
            // ...and when it does, it carries the correct sign.
            (den != 0 && r == Q::PosSat) ==> crate::q::signed_den_num(
                num as int,
                den as int,
            ) > 0,
            (den != 0 && r == Q::NegSat) ==> crate::q::signed_den_num(
                num as int,
                den as int,
            ) < 0,
            // Otherwise the value is pinned completely, to the same nearest-mode
            // rounding of the same sign-normalised pair that `new_rounded` uses.
            (den != 0 && crate::model::magnitude_fits(
                crate::q::signed_den_num(num as int, den as int),
                crate::model::abs_int(den as int),
            )) ==> r == Q::Number(
                crate::round::round_frac(
                    crate::q::signed_den_num(num as int, den as int),
                    crate::model::abs_int(den as int),
                    Dir::Nearest,
                ),
            ),
    {
        if den == 0 {
            if num == 0 {
                Q::Nan
            } else if num > 0 {
                Q::PosInf
            } else {
                Q::NegInf
            }
        } else {
            // Normalise the sign onto the numerator first, matching
            // `new_rounded`'s convention, so that the magnitude test and the
            // rounding agree about which value they are talking about.
            // `0 - (i64::MIN as i128)` is `2^63`, comfortably inside `i128`.
            let n: i128 = if den < 0 {
                0 - (num as i128)
            } else {
                num as i128
            };
            let d: i128 = if den < 0 {
                0 - (den as i128)
            } else {
                den as i128
            };
            proof {
                // `|n| <= 2^63 < 2^126 = num_input_bound()`, which is
                // `magnitude_fits_exec`'s precondition.
                crate::model::lemma_pow2_64();
                crate::model::lemma_pow2_126();
                crate::model::lemma_pow2_mono(64, 126);
            }
            if crate::q::magnitude_fits_exec(n, d) {
                match Rat::new_rounded(num, den, Dir::Nearest) {
                    Some(x) => Q::Number(x),
                    // Unreachable: `new_rounded` is `None` iff `den == 0`.
                    None => Q::Nan,
                }
            } else if n > 0 {
                Q::PosSat
            } else {
                Q::NegSat
            }
        }
    }

    // -----------------------------------------------------------------------
    // Value predicates (issue #26 §5)
    //
    // Each predicate is `false` on `Nan`. The design states that result.
    // `Nan` denotes every value, thus no non-trivial predicate holds of it.
    //
    // These predicates delegate to the verified kernel predicates on `Rat` and
    // do not reimplement the arithmetic. A reimplementation makes a
    // postcondition that mirrors its own body, and a defect that is present in
    // both still verifies. Delegation puts the content in the proven contract
    // of `Rat`.
    // -----------------------------------------------------------------------

    /// Whether this is exactly zero.
    pub open spec fn spec_is_zero(self) -> bool {
        match self {
            Q::Number(x) => x.n() == 0,
            _ => false,
        }
    }

    /// Whether this is exactly one.
    pub open spec fn spec_is_one(self) -> bool {
        match self {
            Q::Number(x) => x.n() == x.d(),
            _ => false,
        }
    }

    /// Whether this is `Number(x)` with `x` the exact rational `n / d`.
    ///
    /// A constructor states its result with this predicate and does not name a
    /// kernel constructor. `Rat::zero()` and the other kernel constructors are
    /// `exec` functions and thus cannot appear in a specification.
    pub open spec fn spec_is_value(self, n: int, d: int) -> bool {
        match self {
            Q::Number(x) => x.n() == n && x.d() == d,
            _ => false,
        }
    }

    /// Whether this lies in `[0, 1]`.
    pub open spec fn spec_in_unit_interval(self) -> bool {
        match self {
            Q::Number(x) => x.n() >= 0 && x.n() <= x.d(),
            _ => false,
        }
    }

    /// `self == 0`.
    ///
    /// The result is false for each special value. `PosSat` denotes
    /// `(MAX_MAG, +∞)`, which does not contain zero, thus false is the true
    /// answer there. For `Nan` the result is a convention from the design.
    pub fn is_zero(self) -> (r: bool)
        requires
            self.wf(),
        ensures
            r == self.spec_is_zero(),
    {
        match self {
            Q::Number(x) => x.is_zero(),
            _ => false,
        }
    }

    /// `self == 1`.
    pub fn is_one(self) -> (r: bool)
        requires
            self.wf(),
        ensures
            r == self.spec_is_one(),
    {
        match self {
            Q::Number(x) => x.is_one(),
            _ => false,
        }
    }

    /// `0 <= self <= 1`.
    ///
    /// The result is false for each special value. For the saturations false is
    /// the true answer, because both saturation ranges are outside `[0, 1]`.
    pub fn in_unit_interval(self) -> (r: bool)
        requires
            self.wf(),
        ensures
            r == self.spec_in_unit_interval(),
    {
        match self {
            Q::Number(x) => x.in_unit_interval(),
            _ => false,
        }
    }

    /// The sign, where one exists.
    ///
    /// The result is `None` for `Nan` only. Both saturations and both
    /// infinities have a definite sign and give `Some`. The discriminant
    /// carries that sign for this purpose.
    pub fn signum(self) -> (r: Option<Sign>)
        requires
            self.wf(),
        ensures
            r.is_none() <==> self.spec_is_nan(),
            self.spec_is_zero() ==> r == Some(Sign::Zero),
    {
        match self {
            Q::Number(x) => {
                let s = x.signum();
                if s < 0 {
                    Some(Sign::Negative)
                } else if s > 0 {
                    Some(Sign::Positive)
                } else {
                    Some(Sign::Zero)
                }
            },
            Q::PosSat => Some(Sign::Positive),
            Q::NegSat => Some(Sign::Negative),
            Q::PosInf => Some(Sign::Positive),
            Q::NegInf => Some(Sign::Negative),
            Q::Nan => None,
        }
    }
}

// ---------------------------------------------------------------------------
// N-ary folds (issue #26 §10.5)
//
// The kernel folds `nary::sum`, `nary::product` and `nary::weighted_mean`
// clamp. For example, `sum(&[M, M, -M])` clamps to `M`, then subtracts, and
// returns `0`, but the true total is `M`. The folds below use the operations of
// this enum, thus an overflow at any point in the chain is reported and not
// absorbed.
//
// Issue #26 §9.2 states the cost. After a partial fold saturates,
// `PosSat + Number(-M)` is `Nan`, and the fold does not recover. A sequence of
// representable numbers with a representable total can thus give `Nan`. This
// behaviour is less useful than the sticky infinities of `f64`, but it does not
// give a wrong number. A caller that needs the exact-path guarantee must check
// `is_number()` on the result. That check is the hypothesis "all partial folds
// are `Number`" from §9.2.
// ---------------------------------------------------------------------------

/// Every element satisfies the type invariant.
pub open spec fn all_wf_q(s: Seq<Q>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> (#[trigger] s[i]).wf()
}

/// Every component of every pair satisfies the type invariant.
pub open spec fn all_wf_q_pairs(s: Seq<(Q, Q)>) -> bool {
    forall|i: int|
        0 <= i < s.len() ==> (#[trigger] s[i]).0.wf() && s[i].1.wf()
}

impl Q {
    /// `xs[0] + xs[1] + ...`, left to right. An empty slice gives `0`.
    ///
    /// The left-to-right order is part of the contract and not an
    /// implementation detail. With rounding, addition is not associative, thus
    /// the order fixes the answer and makes the result reproducible.
    pub fn sum(xs: &[Q]) -> (r: Q)
        requires
            all_wf_q(xs@),
        ensures
            r.wf(),
            xs@.len() == 0 ==> r.spec_is_zero(),
    {
        let mut acc = Q::zero();
        let mut i: usize = 0;
        while i < xs.len()
            invariant
                acc.wf(),
                all_wf_q(xs@),
                i <= xs.len(),
                i == 0 ==> acc.spec_is_zero(),
            decreases xs.len() - i,
        {
            acc = Q::add(acc, xs[i]);
            i = i + 1;
        }
        acc
    }

    /// `xs[0] * xs[1] * ...`, left to right. An empty slice gives `1`.
    pub fn product(xs: &[Q]) -> (r: Q)
        requires
            all_wf_q(xs@),
        ensures
            r.wf(),
            xs@.len() == 0 ==> r.spec_is_one(),
    {
        let mut acc = Q::one();
        let mut i: usize = 0;
        while i < xs.len()
            invariant
                acc.wf(),
                all_wf_q(xs@),
                i <= xs.len(),
                i == 0 ==> acc.spec_is_one(),
            decreases xs.len() - i,
        {
            acc = Q::mul(acc, xs[i]);
            i = i + 1;
        }
        acc
    }

    /// `sum(w_i · x_i) / sum(w_i)` over `(weight, value)` pairs.
    ///
    /// This function is total. The kernel function returns `Option`. A zero
    /// total weight is not an out-of-band failure here. The result is `Nan`
    /// when the weighted numerator is also zero, because `0/0` carries no
    /// information. Otherwise the result is a signed infinity, by the #26 §4
    /// convention that each division follows. An empty slice gives `Nan` for
    /// that reason, and not by a special case.
    pub fn weighted_mean(pairs: &[(Q, Q)]) -> (r: Q)
        requires
            all_wf_q_pairs(pairs@),
        ensures
            r.wf(),
    {
        let mut acc_num = Q::zero();
        let mut acc_w = Q::zero();
        let mut i: usize = 0;
        while i < pairs.len()
            invariant
                acc_num.wf(),
                acc_w.wf(),
                all_wf_q_pairs(pairs@),
                i <= pairs.len(),
            decreases pairs.len() - i,
        {
            let (w, x) = pairs[i];
            acc_num = Q::add(acc_num, Q::mul(w, x));
            acc_w = Q::add(acc_w, w);
            i = i + 1;
        }
        Q::div(acc_num, acc_w)
    }
}

// ---------------------------------------------------------------------------
// Addition, subtraction, multiplication (issue #26 §10.3)
//
// Saturation becomes visible in the enum here. The kernel returns `±MAX_MAG/1`
// when a sum or a product leaves the budget. For example, `Rat::add(M, M)` is
// `M`, which is wrong by a factor of two and looks like a true result. This
// layer reports `PosSat` or `NegSat` instead.
//
// The precision cliffs below are option (A) from §6. The lattice has no element
// for "sign known, magnitude unknown", thus some cells give `Nan` where a
// `PosUnknown` or `NegUnknown` state gives a precise answer. A cliff affects
// only a computation that continues after an overflow.
// ---------------------------------------------------------------------------

impl Q {
    /// `x + y` for two representable rationals, saturating rather than clamping.
    fn add_numbers(x: Rat, y: Rat) -> (r: Q)
        requires
            x.wf(),
            y.wf(),
        ensures
            r.wf(),
            !r.spec_is_nan(),
            !r.spec_is_infinite(),
    {
        let n: i128 = crate::q::add_n_exec(x, y);
        let d: i128 = crate::q::prod_d_exec(x, y);
        proof {
            crate::q::lemma_op_widths(x, y);
            crate::model::lemma_pow2_126();
        }
        if crate::q::magnitude_fits_exec(n, d) {
            Q::Number(Rat::add(x, y))
        } else if n > 0 {
            Q::PosSat
        } else {
            Q::NegSat
        }
    }

    /// `x * y` for two representable rationals, saturating rather than clamping.
    fn mul_numbers(x: Rat, y: Rat) -> (r: Q)
        requires
            x.wf(),
            y.wf(),
        ensures
            r.wf(),
            !r.spec_is_nan(),
            !r.spec_is_infinite(),
    {
        let n: i128 = crate::q::mul_n_exec(x, y);
        let d: i128 = crate::q::prod_d_exec(x, y);
        proof {
            crate::q::lemma_op_widths(x, y);
            crate::model::lemma_pow2_126();
        }
        if crate::q::magnitude_fits_exec(n, d) {
            Q::Number(Rat::mul(x, y))
        } else if n > 0 {
            Q::PosSat
        } else {
            Q::NegSat
        }
    }

    /// `Number(x) + Sat`, where `sat_pos` says which saturation.
    ///
    /// `Number(x) + PosSat` denotes `(MAX_MAG + x, +∞)`. For `x >= 0` that
    /// interval is inside `⟦PosSat⟧`, and the answer is sound. For `x < 0` the
    /// lower endpoint `MAX_MAG + x` can be as low as `0`. The image then
    /// contains representable values, and a `PosSat` result is unsound. This is
    /// the cliff.
    fn number_plus_sat(x: Rat, sat_pos: bool) -> (r: Q)
        requires
            x.wf(),
        ensures
            r.wf(),
            !r.spec_is_infinite(),
            !r.spec_is_number(),
    {
        let s = x.signum();
        if sat_pos {
            if s >= 0 {
                Q::PosSat
            } else {
                Q::Nan
            }
        } else {
            if s <= 0 {
                Q::NegSat
            } else {
                Q::Nan
            }
        }
    }

    /// `Number(x) * Sat`, where `sat_pos` says which saturation.
    ///
    /// The boundary is inclusive. At `|x| == 1` the image is exactly
    /// `1 · (MAX_MAG, ∞) = (MAX_MAG, ∞)`, thus saturation is sound and minimal
    /// there. The cliff is the open interval `0 < |x| < 1`, where the image
    /// `(MAX_MAG·|x|, ∞)` extends below `MAX_MAG`. The condition must not be
    /// `x > 1`: that form sends `one() * PosSat` to `Nan` and contradicts
    /// `neg(PosSat) == NegSat`.
    ///
    /// `Number(0) * Sat` is exactly `Number(0)`, and not `Nan`, because `Sat`
    /// denotes finite reals only. This is the clearest case where saturation is
    /// better behaved than infinity, because `0 · ±∞` is indeterminate.
    fn number_times_sat(x: Rat, sat_pos: bool) -> (r: Q)
        requires
            x.wf(),
        ensures
            r.wf(),
            !r.spec_is_infinite(),
    {
        if x.is_zero() {
            return Q::zero();
        }
        let n = x.numerator();
        let d = x.denominator();
        // `|x| >= 1` without division: `|n| >= d`, and `d > 0` by the invariant.
        let at_least_one = n >= d || n <= 0 - d;
        if !at_least_one {
            return Q::Nan;
        }
        // Sign of the product of a sign-definite saturation and a nonzero `x`.
        let positive = (n > 0) == sat_pos;
        if positive {
            Q::PosSat
        } else {
            Q::NegSat
        }
    }

    /// `a + b`, total.
    ///
    /// This operation replaces the kernel `add`, which clamps.
    /// `Rat::add(MAX_MAG, MAX_MAG)` returns `MAX_MAG/1`. That result is wrong
    /// by a factor of two, carries no error guarantee, and looks like a true
    /// result unless the caller uses `checked_add`.
    pub fn add(a: Q, b: Q) -> (r: Q)
        requires
            a.wf(),
            b.wf(),
        ensures
            r.wf(),
            a.spec_is_nan() ==> r.spec_is_nan(),
            b.spec_is_nan() ==> r.spec_is_nan(),
            // Two representable rationals can only overflow, never become
            // infinite and never lose all information.
            (a.spec_is_number() && b.spec_is_number()) ==> (r.spec_is_number()
                || r.spec_is_saturated()),
            // An infinite result needs an infinite operand. Addition cannot
            // create one. `is_infinite()` thus keeps the meaning "a division by
            // zero occurred upstream".
            r.spec_is_infinite() ==> (a.spec_is_infinite() || b.spec_is_infinite()),
            // ...and conversely an infinite operand always survives, so no
            // representable sum can come out of one.
            (a.spec_is_infinite() || b.spec_is_infinite()) ==> !r.spec_is_number(),
    {
        match (a, b) {
            (Q::Nan, _) => Q::Nan,
            (_, Q::Nan) => Q::Nan,
            (Q::Number(x), Q::Number(y)) => Q::add_numbers(x, y),
            (Q::Number(x), Q::PosSat) => Q::number_plus_sat(x, true),
            (Q::Number(x), Q::NegSat) => Q::number_plus_sat(x, false),
            (Q::PosSat, Q::Number(y)) => Q::number_plus_sat(y, true),
            (Q::NegSat, Q::Number(y)) => Q::number_plus_sat(y, false),
            // Same-signed saturations reinforce; opposite-signed ones cancel to
            // something entirely unknown.
            (Q::PosSat, Q::PosSat) => Q::PosSat,
            (Q::NegSat, Q::NegSat) => Q::NegSat,
            (Q::PosSat, Q::NegSat) => Q::Nan,
            (Q::NegSat, Q::PosSat) => Q::Nan,
            // An infinity dominates anything finite, saturated or not.
            (Q::PosInf, Q::NegInf) => Q::Nan,
            (Q::NegInf, Q::PosInf) => Q::Nan,
            (Q::PosInf, _) => Q::PosInf,
            (Q::NegInf, _) => Q::NegInf,
            (_, Q::PosInf) => Q::PosInf,
            (_, Q::NegInf) => Q::NegInf,
        }
    }

    /// `a - b`, total.
    ///
    /// The definition is `a + (-b)`, as §5 specifies. The two operations thus
    /// agree for an overflowing difference.
    pub fn sub(a: Q, b: Q) -> (r: Q)
        requires
            a.wf(),
            b.wf(),
        ensures
            r.wf(),
            a.spec_is_nan() ==> r.spec_is_nan(),
            b.spec_is_nan() ==> r.spec_is_nan(),
    {
        Q::add(a, b.neg())
    }

    /// `a * b`, total.
    pub fn mul(a: Q, b: Q) -> (r: Q)
        requires
            a.wf(),
            b.wf(),
        ensures
            r.wf(),
            a.spec_is_nan() ==> r.spec_is_nan(),
            b.spec_is_nan() ==> r.spec_is_nan(),
            (a.spec_is_number() && b.spec_is_number()) ==> (r.spec_is_number()
                || r.spec_is_saturated()),
            r.spec_is_infinite() ==> (a.spec_is_infinite() || b.spec_is_infinite()),
            // An infinite operand gives an infinity or `Nan`, and never a
            // representable product. Against zero the result is `Nan`.
            (a.spec_is_infinite() || b.spec_is_infinite()) ==> !r.spec_is_number(),
    {
        match (a, b) {
            (Q::Nan, _) => Q::Nan,
            (_, Q::Nan) => Q::Nan,
            (Q::Number(x), Q::Number(y)) => Q::mul_numbers(x, y),
            (Q::Number(x), Q::PosSat) => Q::number_times_sat(x, true),
            (Q::Number(x), Q::NegSat) => Q::number_times_sat(x, false),
            (Q::PosSat, Q::Number(y)) => Q::number_times_sat(y, true),
            (Q::NegSat, Q::Number(y)) => Q::number_times_sat(y, false),
            // `0 · ±∞` is indeterminate. `0 · Sat` is exactly zero.
            (Q::Number(x), Q::PosInf) => Q::number_times_inf(x, true),
            (Q::Number(x), Q::NegInf) => Q::number_times_inf(x, false),
            (Q::PosInf, Q::Number(y)) => Q::number_times_inf(y, true),
            (Q::NegInf, Q::Number(y)) => Q::number_times_inf(y, false),
            // Two saturations give a saturation with the product sign. A
            // product of two magnitudes above MAX_MAG is far above MAX_MAG.
            (Q::PosSat, Q::PosSat) => Q::PosSat,
            (Q::PosSat, Q::NegSat) => Q::NegSat,
            (Q::NegSat, Q::PosSat) => Q::NegSat,
            (Q::NegSat, Q::NegSat) => Q::PosSat,
            (Q::PosSat, Q::PosInf) => Q::PosInf,
            (Q::PosSat, Q::NegInf) => Q::NegInf,
            (Q::NegSat, Q::PosInf) => Q::NegInf,
            (Q::NegSat, Q::NegInf) => Q::PosInf,
            (Q::PosInf, Q::PosSat) => Q::PosInf,
            (Q::PosInf, Q::NegSat) => Q::NegInf,
            (Q::NegInf, Q::PosSat) => Q::NegInf,
            (Q::NegInf, Q::NegSat) => Q::PosInf,
            (Q::PosInf, Q::PosInf) => Q::PosInf,
            (Q::PosInf, Q::NegInf) => Q::NegInf,
            (Q::NegInf, Q::PosInf) => Q::NegInf,
            (Q::NegInf, Q::NegInf) => Q::PosInf,
        }
    }

    /// `self` raised to `e`, total.
    ///
    /// `pow_u32(a, 0)` is `Number(1)` for each `a`, including `Nan`. This
    /// result matches `NaN^0 == 1` in IEEE 754, and #26 §5 states it. The
    /// exponent is a count and not a value, thus the information in the base
    /// does not apply when the base is used zero times.
    ///
    /// The implementation is a left fold of [`Q::mul`], with the same shape as
    /// the kernel `pow_u32`. The two thus associate their roundings in the same
    /// way. With rounding, multiplication is not associative, thus a
    /// square-and-multiply implementation can give a different answer.
    pub fn pow_u32(self, e: u32) -> (r: Q)
        requires
            self.wf(),
        ensures
            r.wf(),
            e == 0 ==> r.spec_is_one(),
    {
        let mut acc = Q::one();
        let mut i: u32 = 0;
        while i < e
            invariant
                acc.wf(),
                self.wf(),
                i <= e,
                i == 0 ==> acc.spec_is_one(),
            decreases e - i,
        {
            acc = Q::mul(acc, self);
            i = i + 1;
        }
        acc
    }

    /// `a + b` when the result is a representable rational, `None` otherwise.
    ///
    /// Issue #26 §3 applies. The four kernel `checked_*` contracts are
    /// `r.is_none() <==> saturated(...)`, thus the discriminant carries the
    /// same information and these functions are a convenience. The equivalence
    /// is provable. These functions also cannot panic, unlike the kernel
    /// versions.
    pub fn checked_add(a: Q, b: Q) -> (r: Option<Rat>)
        requires
            a.wf(),
            b.wf(),
        ensures
            r.is_some() ==> r.unwrap().wf(),
            (a.spec_is_nan() || b.spec_is_nan()) ==> r.is_none(),
            (a.spec_is_infinite() || b.spec_is_infinite()) ==> r.is_none(),
    {
        match Q::add(a, b) {
            Q::Number(f) => Some(f),
            _ => None,
        }
    }

    /// `a - b` when the result is a representable rational. See
    /// [`Q::checked_add`].
    pub fn checked_sub(a: Q, b: Q) -> (r: Option<Rat>)
        requires
            a.wf(),
            b.wf(),
        ensures
            r.is_some() ==> r.unwrap().wf(),
            (a.spec_is_nan() || b.spec_is_nan()) ==> r.is_none(),
    {
        match Q::sub(a, b) {
            Q::Number(f) => Some(f),
            _ => None,
        }
    }

    /// `a * b` when the result is a representable rational. See
    /// [`Q::checked_add`].
    ///
    /// This function can succeed with a saturated operand. `Number(0) * PosSat`
    /// is exactly `Number(0)`. There is thus no rule "a saturated input gives
    /// `None`", which `checked_add` has.
    pub fn checked_mul(a: Q, b: Q) -> (r: Option<Rat>)
        requires
            a.wf(),
            b.wf(),
        ensures
            r.is_some() ==> r.unwrap().wf(),
            (a.spec_is_nan() || b.spec_is_nan()) ==> r.is_none(),
            (a.spec_is_infinite() || b.spec_is_infinite()) ==> r.is_none(),
    {
        match Q::mul(a, b) {
            Q::Number(f) => Some(f),
            _ => None,
        }
    }

    /// `Number(x) * ±∞`. Zero times an infinity is the classic indeterminate.
    fn number_times_inf(x: Rat, inf_pos: bool) -> (r: Q)
        requires
            x.wf(),
        ensures
            r.wf(),
            !r.spec_is_number(),
            !r.spec_is_saturated(),
    {
        let s = x.signum();
        if s == 0 {
            Q::Nan
        } else if (s > 0) == inf_pos {
            Q::PosInf
        } else {
            Q::NegInf
        }
    }
}

// ---------------------------------------------------------------------------
// Negation and absolute value (issue #26 §5)
//
// These two operations are the only entries in the design that are exact and
// total and have no precision cliff. Negation is a bijection on each state.
// Absolute value maps the two sign-definite pairs onto their positive halves.
// ---------------------------------------------------------------------------

impl Q {
    /// `-self`. Exact and total.
    ///
    /// Negation is sound on the saturations. `⟦PosSat⟧ = (MAX_MAG, ∞)` negates
    /// onto `⟦NegSat⟧ = (-∞, -MAX_MAG)`, thus the denotation is symmetric and
    /// the operation loses no information. The kernel negation cannot overflow:
    /// `|num| <= MAX_MAG` keeps the result clear of `i64::MIN`.
    pub fn neg(self) -> (r: Q)
        requires
            self.wf(),
        ensures
            r.wf(),
            // Negation permutes the classes rather than collapsing any of them.
            r.spec_is_number() == self.spec_is_number(),
            r.spec_is_saturated() == self.spec_is_saturated(),
            r.spec_is_infinite() == self.spec_is_infinite(),
            r.spec_is_nan() == self.spec_is_nan(),
            r.spec_is_zero() == self.spec_is_zero(),
    {
        match self {
            Q::Number(x) => Q::Number(x.neg()),
            Q::PosSat => Q::NegSat,
            Q::NegSat => Q::PosSat,
            Q::PosInf => Q::NegInf,
            Q::NegInf => Q::PosInf,
            Q::Nan => Q::Nan,
        }
    }

    /// `|self|`. Exact and total.
    ///
    /// `abs` is not injective. It maps both saturations to `PosSat` and both
    /// infinities to `PosInf`. This behaviour is correct, and it is the reason
    /// that `neg` above carries the class-preservation postconditions and this
    /// function does not.
    pub fn abs(self) -> (r: Q)
        requires
            self.wf(),
        ensures
            r.wf(),
            r.spec_is_number() == self.spec_is_number(),
            r.spec_is_saturated() == self.spec_is_saturated(),
            r.spec_is_infinite() == self.spec_is_infinite(),
            r.spec_is_nan() == self.spec_is_nan(),
            // The result is never negative: a `Number` payload is `>= 0`, and
            // the only special that survives is the positive one of each pair.
            r.spec_is_number() ==> r->Number_0.n() >= 0,
            !r.spec_is_nan() ==> r != Q::NegSat && r != Q::NegInf,
    {
        match self {
            Q::Number(x) => Q::Number(x.abs()),
            Q::PosSat => Q::PosSat,
            Q::NegSat => Q::PosSat,
            Q::PosInf => Q::PosInf,
            Q::NegInf => Q::PosInf,
            Q::Nan => Q::Nan,
        }
    }
}

// ---------------------------------------------------------------------------
// Selection: min, max, clamp (issue #26 §5)
//
// These operations propagate `Nan`. They are thus not the `Ord`-based selection
// that `slice.iter().min()` performs. A selection that comes from the order is
// a defect: `Ord`-based selection gives `min(Nan, Number(5)) == Number(5)`,
// which asserts that the true value is exactly 5 when the value can be
// anything.
//
// IEEE 754 has settled this question. The `minNum` and `maxNum` operations of
// 754-2008 returned the non-NaN operand. 754-2019 withdrew them and replaced
// them with the NaN-propagating `minimum` and `maximum`. The ignore-NaN
// behaviour has the separate names `minimumNumber` and `maximumNumber`.
// Section 4 takes IEEE 754 as the reference model, thus these operations have
// `minimum` semantics.
//
// For the sign-definite special values these operations follow the §5 order.
// That order is sound for those variants.
// ---------------------------------------------------------------------------

impl Q {
    /// The smaller of `a` and `b`, propagating `Nan`.
    ///
    /// This function does not agree with `Ord`-based selection, by design. A
    /// fold of this function is not `slice.iter().min()`. This function returns
    /// `Nan` if any input is `Nan`. `Ord`-based selection returns the other
    /// operand and thus asserts a value that the result does not have.
    pub fn min(a: Q, b: Q) -> (r: Q)
        requires
            a.wf(),
            b.wf(),
        ensures
            r.wf(),
            (a.spec_is_nan() || b.spec_is_nan()) ==> r.spec_is_nan(),
            !(a.spec_is_nan() || b.spec_is_nan()) ==> {
                &&& (r == a || r == b)
                &&& Q::spec_le(r, a)
                &&& Q::spec_le(r, b)
                // ...and which argument. The contract thus names the result
                // and does not only constrain it.
                //
                // The three clauses above fix the answer uniquely, which is
                // `theorem_min_spec_categorical`. That uniqueness is a property
                // of the contract. These two clauses connect it to the output
                // of this function, thus the postcondition determines the
                // result for each input.
                &&& Q::spec_le(a, b) ==> r == a
                &&& !Q::spec_le(a, b) ==> r == b
            },
    {
        if a.is_nan() || b.is_nan() {
            Q::Nan
        } else if Q::le(a, b) {
            a
        } else {
            b
        }
    }

    /// The larger of `a` and `b`, propagating `Nan`. See [`Q::min`].
    pub fn max(a: Q, b: Q) -> (r: Q)
        requires
            a.wf(),
            b.wf(),
        ensures
            r.wf(),
            (a.spec_is_nan() || b.spec_is_nan()) ==> r.spec_is_nan(),
            !(a.spec_is_nan() || b.spec_is_nan()) ==> {
                &&& (r == a || r == b)
                &&& Q::spec_le(a, r)
                &&& Q::spec_le(b, r)
                // See `Q::min`: these name the result rather than bounding it.
                &&& Q::spec_le(a, b) ==> r == b
                &&& !Q::spec_le(a, b) ==> r == a
            },
    {
        if a.is_nan() || b.is_nan() {
            Q::Nan
        } else if Q::le(a, b) {
            b
        } else {
            a
        }
    }

    /// `a` clamped into `[lo, hi]`, propagating `Nan`.
    ///
    /// A `Nan` in any of the three arguments gives `Nan`. This includes a
    /// bound. A range whose endpoint carries no information gives no
    /// informative answer. A `hi` result there is the `clamp(Nan, lo, hi) == hi`
    /// defect that §5 names.
    ///
    /// This function does not require `lo <= hi`, unlike the kernel `clamp`.
    /// `Nan` is an admissible bound, thus the order alone cannot state the
    /// precondition. An inverted range gives `Nan` and not an endpoint, because
    /// an endpoint asserts a false statement.
    pub fn clamp(a: Q, lo: Q, hi: Q) -> (r: Q)
        requires
            a.wf(),
            lo.wf(),
            hi.wf(),
        ensures
            r.wf(),
            (a.spec_is_nan() || lo.spec_is_nan() || hi.spec_is_nan()) ==> r.spec_is_nan(),
            (!a.spec_is_nan() && !lo.spec_is_nan() && !hi.spec_is_nan() && Q::spec_le(lo, hi)) ==> {
                &&& (r == a || r == lo || r == hi)
                &&& Q::spec_le(lo, r)
                &&& Q::spec_le(r, hi)
                // ...and which of the three values. Without these three
                // clauses a `clamp` that always returns `lo` satisfies the
                // contract above: for `lo < a < hi`, `r == lo` is one of the
                // three permitted values and lies in `[lo, hi]`.
                //
                // A postcondition that is wide enough to admit a wrong answer
                // is not a specification. A proof that the contract is
                // categorical finds this class of weakness.
                &&& (Q::spec_le(lo, a) && Q::spec_le(a, hi)) ==> r == a
                &&& !Q::spec_le(lo, a) ==> r == lo
                &&& !Q::spec_le(a, hi) ==> r == hi
            },
    {
        if a.is_nan() || lo.is_nan() || hi.is_nan() {
            Q::Nan
        } else if Q::lt(hi, lo) {
            // An inverted range has no consistent answer. `Nan` states that
            // condition. An endpoint result does not.
            Q::Nan
        } else if Q::lt(a, lo) {
            proof {
                // `a < lo <= hi` gives `a <= hi`, which makes the "returns
                // `hi`" clause vacuously true on this branch. Transitivity is
                // not free: the prover has `!spec_le(lo, a)` and needs totality
                // to turn it into `spec_le(a, lo)` first.
                theorem_order_total(lo, a);
                theorem_order_transitive(a, lo, hi);
            }
            lo
        } else if Q::lt(hi, a) {
            hi
        } else {
            a
        }
    }
}

// ---------------------------------------------------------------------------
// Total division (issue #26 §10.2)
//
// This section closes the three defects that open #26. The kernel now fails
// loudly on each of them, and this layer answers with a value instead:
//
//   * `Rat::zero().recip()` panics. It once returned `Rat { num: -1, den: 0 }`,
//     which violates the type invariant and fails later, far from the cause.
//   * `Rat::div(x, 0)` panics.
//   * `Rat::checked_div(x, 0)` is `None`, as `std` and `num-traits` are for
//     this case.
//
// Each cell below comes from the denotations in §2. The result is the smallest
// state whose denotation contains the true image
// `{ x/y : x ∈ ⟦a⟧, y ∈ ⟦b⟧ }`. `Nan` is always sound, because it denotes
// every value. Precision is thus the only property to argue.
// ---------------------------------------------------------------------------

impl Q {
    /// `x / y` for two representable rationals with `y != 0`.
    ///
    /// This operation saturates and does not clamp. The kernel `Rat::div`
    /// returns `±MAX_MAG/1` when the exact quotient leaves the budget. That
    /// result is a singleton denotation that does not contain the true value. A
    /// `PosSat` or `NegSat` result keeps the denotation sound.
    fn div_numbers(x: Rat, y: Rat) -> (r: Q)
        requires
            x.wf(),
            y.wf(),
            y.n() != 0,
        ensures
            r.wf(),
            !r.spec_is_nan(),
            !r.spec_is_infinite(),
    {
        let n: i128 = crate::q::div_n_exec(x, y);
        let d: i128 = crate::q::div_d_exec(x, y);
        proof {
            crate::q::lemma_op_widths(x, y);
            crate::model::lemma_pow2_126();
        }
        if crate::q::magnitude_fits_exec(n, d) {
            Q::Number(Rat::div(x, y))
        } else if n > 0 {
            Q::PosSat
        } else {
            Q::NegSat
        }
    }

    /// A saturation divided by a representable rational.
    ///
    /// `pos` selects the saturation of the numerator. For `y > 0` the image of
    /// `(MAX_MAG, ∞) / y` is `(MAX_MAG/y, ∞)`. That image stays inside
    /// `⟦PosSat⟧` while `MAX_MAG/y >= MAX_MAG`, thus while `y <= 1`. Above the
    /// unit boundary the image contains representable values, and no saturation
    /// state is sound. This is the precision cliff of §6. The boundary is
    /// inclusive: at `y == 1` the image is exactly `⟦PosSat⟧`.
    fn sat_div_number(pos: bool, y: Rat) -> (r: Q)
        requires
            y.wf(),
        ensures
            r.wf(),
            // A saturation is finite, so the quotient can only become infinite
            // by dividing by zero. `div` needs this to prove that an infinity in
            // its result always points at a zero divisor.
            r.spec_is_infinite() ==> y.n() == 0,
            // ...and conversely, a zero divisor always produces one, so no
            // representable quotient can survive it.
            y.n() == 0 ==> r.spec_is_infinite(),
    {
        let s = y.signum();
        if s == 0 {
            // A saturation has a definite sign and is nonzero, thus this case
            // is `x/0` with `x != 0`. The IEEE convention of §4 gives a signed
            // infinity.
            if pos {
                Q::PosInf
            } else {
                Q::NegInf
            }
        } else if s > 0 {
            if y.numerator() <= y.denominator() {
                if pos {
                    Q::PosSat
                } else {
                    Q::NegSat
                }
            } else {
                Q::Nan
            }
        } else {
            if y.numerator() >= 0 - y.denominator() {
                if pos {
                    Q::NegSat
                } else {
                    Q::PosSat
                }
            } else {
                Q::Nan
            }
        }
    }

    /// `a / b`, total.
    ///
    /// This operation never panics and never returns a value outside the type
    /// invariant. The division-by-zero cases follow issue #26 §4, which takes
    /// IEEE 754 as the reference model. The rule applies uniformly. A mixed
    /// rule, with the IEEE result for `x/0` and `Nan` for `recip(0)` and
    /// `±∞/0`, breaks `recip(x) == div(one, x)` at `x = 0`.
    ///
    /// Two cells are exact where `Nan` is the expected result:
    ///
    /// * `Sat / Inf` is `Number(0)`. `PosSat` denotes reals only and never
    ///   `±∞`, thus the image is exactly `{s/±∞} = {0}`. Saturation is better
    ///   behaved than infinity here.
    /// * `Inf / Sat` is a signed infinity, for the same reason. `±∞` divided by
    ///   a finite real stays infinite.
    pub fn div(a: Q, b: Q) -> (r: Q)
        requires
            a.wf(),
            b.wf(),
        ensures
            r.wf(),
            // `Nan` is absorbing on both sides — no information in, none out.
            a.spec_is_nan() ==> r.spec_is_nan(),
            b.spec_is_nan() ==> r.spec_is_nan(),
            // Dividing two representable rationals by a nonzero divisor yields a
            // rational or an overflow, never an infinity and never `Nan`. This
            // is what makes the `checked_div` sugar below meaningful.
            (a.spec_is_number() && b.spec_is_number() && !b.spec_is_zero()) ==> (r.spec_is_number()
                || r.spec_is_saturated()),
            // An infinite result means a zero divisor or an infinite
            // numerator, and never an overflow. This property keeps
            // `is_infinite()` usable as a diagnostic. It reports a division by
            // zero, and an overflow reports `is_saturated()` instead.
            r.spec_is_infinite() ==> (a.spec_is_infinite() || b.spec_is_zero()),
            // No representable quotient survives a zero divisor or an infinite
            // numerator. Together with the clauses above this is what makes
            // `checked_div` a faithful `Option` view of the discriminant.
            b.spec_is_zero() ==> !r.spec_is_number(),
            a.spec_is_infinite() ==> !r.spec_is_number(),
    {
        match (a, b) {
            (Q::Nan, _) => Q::Nan,
            (_, Q::Nan) => Q::Nan,
            // --- a representable numerator ---
            (Q::Number(x), Q::Number(y)) => {
                if y.is_zero() {
                    if x.is_zero() {
                        // 0/0 carries no information at all.
                        Q::Nan
                    } else if x.signum() > 0 {
                        Q::PosInf
                    } else {
                        Q::NegInf
                    }
                } else {
                    Q::div_numbers(x, y)
                }
            },
            // `x / Sat`: the image is `(0, x/M)`, which contains representable
            // values. Only `x == 0` thus has a sound answer, and that answer is
            // exact, because `Sat` cannot be infinite.
            (Q::Number(x), Q::PosSat) => if x.is_zero() {
                Q::zero()
            } else {
                Q::Nan
            },
            (Q::Number(x), Q::NegSat) => if x.is_zero() {
                Q::zero()
            } else {
                Q::Nan
            },
            (Q::Number(_), Q::PosInf) => Q::zero(),
            (Q::Number(_), Q::NegInf) => Q::zero(),
            // --- a saturated numerator ---
            (Q::PosSat, Q::Number(y)) => Q::sat_div_number(true, y),
            (Q::NegSat, Q::Number(y)) => Q::sat_div_number(false, y),
            // `Sat / Sat` covers `(0, ∞)` or its mirror. The sign is known and
            // the magnitude is unknown. This lattice has no state for that.
            (Q::PosSat, Q::PosSat) => Q::Nan,
            (Q::PosSat, Q::NegSat) => Q::Nan,
            (Q::NegSat, Q::PosSat) => Q::Nan,
            (Q::NegSat, Q::NegSat) => Q::Nan,
            // `Sat / Inf` — exact, see the doc comment.
            (Q::PosSat, Q::PosInf) => Q::zero(),
            (Q::PosSat, Q::NegInf) => Q::zero(),
            (Q::NegSat, Q::PosInf) => Q::zero(),
            (Q::NegSat, Q::NegInf) => Q::zero(),
            // --- an infinite numerator ---
            // Including `y == 0`: §4 makes `±∞/0` sign-preserving, not `Nan`.
            (Q::PosInf, Q::Number(y)) => if y.signum() < 0 {
                Q::NegInf
            } else {
                Q::PosInf
            },
            (Q::NegInf, Q::Number(y)) => if y.signum() < 0 {
                Q::PosInf
            } else {
                Q::NegInf
            },
            (Q::PosInf, Q::PosSat) => Q::PosInf,
            (Q::PosInf, Q::NegSat) => Q::NegInf,
            (Q::NegInf, Q::PosSat) => Q::NegInf,
            (Q::NegInf, Q::NegSat) => Q::PosInf,
            // `∞/∞` is the classic indeterminate.
            (Q::PosInf, Q::PosInf) => Q::Nan,
            (Q::PosInf, Q::NegInf) => Q::Nan,
            (Q::NegInf, Q::PosInf) => Q::Nan,
            (Q::NegInf, Q::NegInf) => Q::Nan,
        }
    }

    /// `1 / self`, total.
    ///
    /// The definition is `div(one, self)` and not a separate case analysis.
    /// This choice is for correctness. Issue #26 §4 records that separate
    /// answers for `recip(0)` and `x/0` break `recip(x) == div(one, x)` at
    /// `x = 0`. One definition from the other makes that divergence
    /// impossible. See `theorem_recip_is_div_one`.
    ///
    /// On a nonzero `Number` the result is exact. Reciprocation swaps the
    /// components of a canonical pair, and both components are inside the
    /// budget. No rounding and no saturation can thus occur.
    ///
    /// This operation is total where the kernel `Rat::recip` carries
    /// `n() != 0` as a precondition and panics at zero.
    pub fn recip(self) -> (r: Q)
        requires
            self.wf(),
        ensures
            r.wf(),
            self.spec_is_nan() ==> r.spec_is_nan(),
    {
        // This contract does not state the cell-by-cell behaviour, such as
        // `recip(0) == PosInf`, `recip(±∞) == 0`, and an exact result for a
        // nonzero rational. A derivation of that behaviour needs the `div`
        // postcondition to reproduce the whole propagation table in ghost form.
        // A specification with the same shape as the table that it specifies is
        // circular, and it verifies with a defect that is present in both.
        //
        // `tests/extended_q.rs` pins the table exhaustively instead. The state
        // space is 6×6 cells, and the tests enumerate each cell. That check is
        // complete, and it runs against the compiled artifact.
        Q::div(Q::one(), self)
    }

    /// `a / b` when the result is a representable rational, `None` otherwise.
    ///
    /// This function is a view over [`Q::div`], and a proof states that
    /// relation. The `Option` carries the information that the discriminant
    /// carries. This function does not panic on a zero divisor, unlike the
    /// kernel `checked_div`. It returns `None`, as `std` and `num-traits` do
    /// for this case.
    pub fn checked_div(a: Q, b: Q) -> (r: Option<Rat>)
        requires
            a.wf(),
            b.wf(),
        ensures
            r.is_some() ==> r.unwrap().wf(),
            // `None` for each case with no representable quotient: a zero
            // divisor, an operand with no information, or an infinite
            // numerator. The remaining `None` case is an overflow, which the
            // kernel `checked_div` also reports. This function is thus an
            // extension of the kernel function and not a change of meaning.
            (b.spec_is_zero() || a.spec_is_nan() || b.spec_is_nan() || a.spec_is_infinite())
                ==> r.is_none(),
    {
        match Q::div(a, b) {
            Q::Number(f) => Some(f),
            _ => None,
        }
    }
}

// ---------------------------------------------------------------------------
// The classification really is a partition
//
// This property is stated and proven, and not assumed. The four predicates are
// the only supported case split on the type from outside the module. A caller
// that handles all four cases thus handles each state.
// ---------------------------------------------------------------------------

/// The four classification predicates are mutually exclusive and jointly
/// exhaustive.
pub proof fn theorem_classification_partitions(q: Q)
    ensures
// exactly one holds

        (if q.spec_is_number() { 1int } else { 0int }) + (if q.spec_is_saturated() {
            1int
        } else {
            0int
        }) + (if q.spec_is_infinite() { 1int } else { 0int }) + (if q.spec_is_nan() {
            1int
        } else {
            0int
        }) == 1,
{
    match q {
        Q::Number(_) => {},
        Q::PosSat => {},
        Q::NegSat => {},
        Q::PosInf => {},
        Q::NegInf => {},
        Q::Nan => {},
    }
}

/// A saturation is never a number, an infinity or a `Nan` — the fact callers
/// most often want when reading `is_saturated` as an overflow diagnostic.
pub proof fn theorem_saturated_excludes_rest(q: Q)
    requires
        q.spec_is_saturated(),
    ensures
        !q.spec_is_number(),
        !q.spec_is_infinite(),
        !q.spec_is_nan(),
{
}

// ---------------------------------------------------------------------------
// The total order (issue #26 §5)
//
//     NegInf  <  NegSat  <  Number(...)  <  PosSat  <  PosInf  <  Nan
//
// This order applies to representations and not to denoted values. Outside
// `Number` that difference is visible: `PosSat == PosSat` compares `Equal`
// while the two true values can differ. Inside `Number` the order is the order
// on rationals.
//
// The placement is sound at the boundaries. Each `NegSat` value is
// `< -MAX_MAG <=` each `Number`, and each `PosSat` value is `> MAX_MAG >=`
// each `Number`, thus both separations are strict. The position of `Nan` is a
// free choice. `f64::total_cmp` puts a negative NaN first and a positive NaN
// last, thus that analogy is partial.
// ---------------------------------------------------------------------------

impl Q {
    /// The position of a variant in the order above.
    ///
    /// The order uses this rank and not the declaration order. A change to the
    /// variant order thus cannot change the order on values. For the same
    /// reason `Ord` is hand-written and not derived.
    pub open spec fn spec_rank(self) -> int {
        match self {
            Q::NegInf => 0,
            Q::NegSat => 1,
            Q::Number(_) => 2,
            Q::PosSat => 3,
            Q::PosInf => 4,
            Q::Nan => 5,
        }
    }

    /// The ghost order: `a <= b`.
    pub open spec fn spec_le(a: Q, b: Q) -> bool {
        if a.spec_rank() != b.spec_rank() {
            a.spec_rank() < b.spec_rank()
        } else {
            match (a, b) {
                (Q::Number(x), Q::Number(y)) => crate::model::q_le(x, y),
                // Every other equal-rank pair is the same payload-free variant,
                // so the two representations are identical.
                _ => true,
            }
        }
    }

    /// The ghost order: `a == b`, as representations.
    pub open spec fn spec_eq(a: Q, b: Q) -> bool {
        Q::spec_le(a, b) && Q::spec_le(b, a)
    }
}

impl Q {
    /// Three-way comparison: negative, zero or positive as `a < b`, `a == b` or
    /// `a > b` in the order above.
    ///
    /// The comparison is total. There is no incomparable pair, because `Nan`
    /// has a definite position.
    pub fn compare(a: Q, b: Q) -> (r: i32)
        requires
            a.wf(),
            b.wf(),
        ensures
            r <= 0 <==> Q::spec_le(a, b),
            r >= 0 <==> Q::spec_le(b, a),
            r == 0 <==> Q::spec_eq(a, b),
    {
        match (a, b) {
            // This is the only case with a payload. It delegates to the
            // verified kernel comparison and does not cross-multiply again.
            (Q::Number(x), Q::Number(y)) => Rat::compare(x, y),
            _ => {
                let ra = Q::rank_exec(a);
                let rb = Q::rank_exec(b);
                if ra < rb {
                    -1
                } else if ra > rb {
                    1
                } else {
                    0
                }
            },
        }
    }

    /// Exec mirror of [`Q::spec_rank`].
    fn rank_exec(q: Q) -> (r: i32)
        ensures
            r == q.spec_rank(),
    {
        match q {
            Q::NegInf => 0,
            Q::NegSat => 1,
            Q::Number(_) => 2,
            Q::PosSat => 3,
            Q::PosInf => 4,
            Q::Nan => 5,
        }
    }

    /// `a < b`.
    pub fn lt(a: Q, b: Q) -> (r: bool)
        requires
            a.wf(),
            b.wf(),
        ensures
            r <==> !Q::spec_le(b, a),
    {
        Q::compare(a, b) < 0
    }

    /// `a <= b`.
    pub fn le(a: Q, b: Q) -> (r: bool)
        requires
            a.wf(),
            b.wf(),
        ensures
            r <==> Q::spec_le(a, b),
    {
        Q::compare(a, b) <= 0
    }

    /// `a > b`.
    pub fn gt(a: Q, b: Q) -> (r: bool)
        requires
            a.wf(),
            b.wf(),
        ensures
            r <==> !Q::spec_le(a, b),
    {
        Q::compare(a, b) > 0
    }

    /// `a >= b`.
    pub fn ge(a: Q, b: Q) -> (r: bool)
        requires
            a.wf(),
            b.wf(),
        ensures
            r <==> Q::spec_le(b, a),
    {
        Q::compare(a, b) >= 0
    }
}

/// The order is **total**: every pair is comparable.
///
/// IEEE 754 does not have this property. IEEE 754 makes each ordered
/// comparison with `NaN` false, thus `NaN` is incomparable with each value and
/// with itself. Totality is the second intentional departure from IEEE 754 in
/// this design. The first is `Nan == Nan`.
pub proof fn theorem_order_total(a: Q, b: Q)
    requires
        a.wf(),
        b.wf(),
    ensures
        Q::spec_le(a, b) || Q::spec_le(b, a),
{
}

/// The order is antisymmetric **against structural equality**: two values each
/// `<=` the other are the same value.
///
/// The conclusion is `a == b` and not `spec_eq(a, b)`. `spec_eq` is defined as
/// `spec_le(a, b) && spec_le(b, a)`, thus a conclusion of `spec_eq` from those
/// two hypotheses restates the hypotheses and proves nothing. The content of
/// the theorem is that the "equal" of the order is the derived `PartialEq`.
/// That property makes a derived `PartialEq`, `Eq` and `Hash` sound next to a
/// hand-written `Ord`, because `Ord` and `Eq` cannot disagree.
///
/// The `Number` case uses the canonicality result of the kernel. Two
/// well-formed `Rat` values are mathematically equal exactly when they are
/// structurally equal. There is thus no pair of distinct representations that
/// the order must call equal.
pub proof fn theorem_order_antisymmetric(a: Q, b: Q)
    requires
        a.wf(),
        b.wf(),
        Q::spec_le(a, b),
        Q::spec_le(b, a),
    ensures
        a == b,
{
    match (a, b) {
        (Q::Number(x), Q::Number(y)) => {
            crate::laws::lemma_canonical_eq(x, y);
        },
        _ => {},
    }
}

/// `spec_eq` and the derived `PartialEq` are the same relation.
///
/// This theorem is the other direction of the theorem above. Together they
/// give the equivalence that `Ord`/`Eq` consistency needs.
pub proof fn theorem_spec_eq_is_structural_eq(a: Q, b: Q)
    requires
        a.wf(),
        b.wf(),
    ensures
        Q::spec_eq(a, b) <==> a == b,
{
    if Q::spec_eq(a, b) {
        theorem_order_antisymmetric(a, b);
    }
    match (a, b) {
        (Q::Number(x), Q::Number(y)) => {
            crate::laws::lemma_canonical_eq(x, y);
        },
        _ => {},
    }
}

/// The order is transitive.
///
/// The cross-rank cases are integer transitivity on the rank. The all-`Number`
/// case uses the transitivity lemma of the kernel.
pub proof fn theorem_order_transitive(a: Q, b: Q, c: Q)
    requires
        a.wf(),
        b.wf(),
        c.wf(),
        Q::spec_le(a, b),
        Q::spec_le(b, c),
    ensures
        Q::spec_le(a, c),
{
    match (a, b, c) {
        (Q::Number(x), Q::Number(y), Q::Number(z)) => {
            crate::q::lemma_le_trans(x, y, z);
        },
        _ => {},
    }
}

/// Saturation sits strictly outside the numbers, on the correct side.
///
/// This fact makes the placement sound. It states that the order on
/// representations agrees with the order on denoted values wherever both are
/// defined.
pub proof fn theorem_sat_separates_numbers(x: Rat)
    requires
        x.wf(),
    ensures
        Q::spec_le(Q::NegSat, Q::Number(x)),
        Q::spec_le(Q::Number(x), Q::PosSat),
        !Q::spec_le(Q::Number(x), Q::NegSat),
        !Q::spec_le(Q::PosSat, Q::Number(x)),
{
}

/// The order has a bottom and a top, and both are *strict*: `NegInf` sits
/// strictly below every other value and `Nan` strictly above.
///
/// The first two clauses give a fold a starting point. A running minimum can
/// start at `Nan`, and a running maximum can start at `NegInf`, and neither
/// start excludes a value. The strictness clauses make the extremes unique. No
/// other value is at the bottom or at the top, thus `compare(q, NegInf) <= 0`
/// identifies `q` as `NegInf`, and `compare(Nan, q) <= 0` identifies `q` as
/// `Nan`. The theorem needs no `wf` hypothesis, because the placement is a
/// property of the rank structure and not of a payload.
pub proof fn theorem_order_extremes(q: Q)
    ensures
        Q::spec_le(Q::NegInf, q),
        Q::spec_le(q, Q::Nan),
        q != Q::NegInf ==> !Q::spec_le(q, Q::NegInf),
        q != Q::Nan ==> !Q::spec_le(Q::Nan, q),
{
}

/// **Trichotomy**: every pair is in exactly one of the relations `a < b`,
/// `a == b`, `b < a` (with `a < b` spelled `!spec_le(b, a)`, as the exec `lt`
/// spells it).
///
/// Totality alone permits `a <= b` and `b <= a` on two distinct values.
/// Antisymmetry alone permits incomparable pairs. A caller that branches three
/// ways on `compare` needs the conjunction: the three branches cover each pair,
/// and no two branches apply together. The statement counts the true relations,
/// in the style of `theorem_classification_partitions`, and does not use six
/// implications.
pub proof fn theorem_order_trichotomy(a: Q, b: Q)
    requires
        a.wf(),
        b.wf(),
    ensures
        (if !Q::spec_le(b, a) {
            1int
        } else {
            0int
        }) + (if a == b {
            1int
        } else {
            0int
        }) + (if !Q::spec_le(a, b) {
            1int
        } else {
            0int
        }) == 1,
{
    theorem_order_total(a, b);
    if Q::spec_le(a, b) && Q::spec_le(b, a) {
        theorem_order_antisymmetric(a, b);
    }
}

/// **`min`'s postcondition pins its result uniquely.** Any two values that
/// both satisfy it — each is one of the arguments and a lower bound of both —
/// are structurally equal.
///
/// This is a categoricity check. A contract that admits two different answers
/// also admits a defect. The `min` contract admits one answer only. The proof
/// has content: on a tie, where `a` and `b` are mathematically equal, the two
/// candidates can be the two representations, and kernel canonicality, through
/// antisymmetry, makes them one.
pub proof fn theorem_min_spec_categorical(a: Q, b: Q, r1: Q, r2: Q)
    requires
        a.wf(),
        b.wf(),
        r1 == a || r1 == b,
        Q::spec_le(r1, a),
        Q::spec_le(r1, b),
        r2 == a || r2 == b,
        Q::spec_le(r2, a),
        Q::spec_le(r2, b),
    ensures
        r1 == r2,
{
    // r1 <= r2 because r2 is one of {a, b}, and symmetrically; antisymmetry
    // then forces structural equality.
    theorem_order_antisymmetric(r1, r2);
}

/// **`max`'s postcondition pins its result uniquely.** This theorem is the dual
/// of [`theorem_min_spec_categorical`]. It is a separate theorem, because the
/// `max` contract is its own statement and not a rewriting of the `min`
/// contract.
pub proof fn theorem_max_spec_categorical(a: Q, b: Q, r1: Q, r2: Q)
    requires
        a.wf(),
        b.wf(),
        r1 == a || r1 == b,
        Q::spec_le(a, r1),
        Q::spec_le(b, r1),
        r2 == a || r2 == b,
        Q::spec_le(a, r2),
        Q::spec_le(b, r2),
    ensures
        r1 == r2,
{
    theorem_order_antisymmetric(r1, r2);
}

/// **`clamp`'s contract pins its result**: any two values satisfying it are the
/// same value.
///
/// This theorem needs the last three clauses of the `clamp` postcondition.
/// Without them the proof of categoricity fails, and the counterexample is
/// direct: for `lo < a < hi` the value `r == lo` satisfies "is one of `a`,
/// `lo`, `hi`" and "lies in `[lo, hi]`". A `clamp` that ignores `a` and always
/// returns `lo` thus verifies against the weaker contract.
///
/// A postcondition that is wide enough to admit a wrong answer is a defect. A
/// failed categoricity proof identifies that defect.
pub proof fn theorem_clamp_spec_categorical(a: Q, lo: Q, hi: Q, r1: Q, r2: Q)
    requires
        a.wf(),
        lo.wf(),
        hi.wf(),
        Q::spec_le(lo, hi),
        (Q::spec_le(lo, a) && Q::spec_le(a, hi)) ==> r1 == a,
        !Q::spec_le(lo, a) ==> r1 == lo,
        !Q::spec_le(a, hi) ==> r1 == hi,
        (Q::spec_le(lo, a) && Q::spec_le(a, hi)) ==> r2 == a,
        !Q::spec_le(lo, a) ==> r2 == lo,
        !Q::spec_le(a, hi) ==> r2 == hi,
    ensures
        r1 == r2,
{
    // The three guards are exhaustive once `lo <= hi`: if `a` is below `lo` it
    // is below `hi` too, and symmetrically above. Totality supplies the
    // trichotomy that makes the case split complete.
    theorem_order_total(lo, a);
    theorem_order_total(a, hi);
}

/// **`min` and `max` together return both arguments**: the pair
/// `(min(a, b), max(a, b))` is `(a, b)` or `(b, a)` — nothing is duplicated
/// and nothing is lost.
///
/// This theorem permits the use of `min` and `max` as a two-element sort,
/// because the multiset of outputs is the multiset of inputs. It does not
/// follow from either contract alone. Each contract states that its result is
/// one of the arguments, which permits an `a` result from both functions.
/// Antisymmetry excludes that case, except for `a == b`, where both disjuncts
/// hold.
pub proof fn theorem_min_max_exchange(a: Q, b: Q, rmin: Q, rmax: Q)
    requires
        a.wf(),
        b.wf(),
        rmin == a || rmin == b,
        Q::spec_le(rmin, a),
        Q::spec_le(rmin, b),
        rmax == a || rmax == b,
        Q::spec_le(a, rmax),
        Q::spec_le(b, rmax),
    ensures
        (rmin == a && rmax == b) || (rmin == b && rmax == a),
{
    if rmin == a && rmax == a {
        // a <= b from min's bound, b <= a from max's: the arguments coincide.
        theorem_order_antisymmetric(a, b);
    }
    if rmin == b && rmax == b {
        theorem_order_antisymmetric(a, b);
    }
}

/// **`min` computes the greatest lower bound**: a value is below `min(a, b)`
/// exactly when it is below both `a` and `b`.
///
/// The lower-bound clauses of the `min` contract state that the result is a
/// lower bound. This theorem states that the result is the greatest lower
/// bound. That property permits reassociation of a chain of `min` calls, thus
/// `x <= min(a, min(b, c))` unfolds to three independent comparisons. The
/// forward direction is transitivity. It is not a restatement of the
/// hypotheses, which do not mention `q`.
pub proof fn theorem_min_is_glb(a: Q, b: Q, r: Q, q: Q)
    requires
        a.wf(),
        b.wf(),
        q.wf(),
        r == a || r == b,
        Q::spec_le(r, a),
        Q::spec_le(r, b),
    ensures
        Q::spec_le(q, r) <==> (Q::spec_le(q, a) && Q::spec_le(q, b)),
{
    if Q::spec_le(q, r) {
        theorem_order_transitive(q, r, a);
        theorem_order_transitive(q, r, b);
    }
}

/// **`max` computes the least upper bound** — the dual of
/// [`theorem_min_is_glb`].
pub proof fn theorem_max_is_lub(a: Q, b: Q, r: Q, q: Q)
    requires
        a.wf(),
        b.wf(),
        q.wf(),
        r == a || r == b,
        Q::spec_le(a, r),
        Q::spec_le(b, r),
    ensures
        Q::spec_le(r, q) <==> (Q::spec_le(a, q) && Q::spec_le(b, q)),
{
    if Q::spec_le(r, q) {
        theorem_order_transitive(a, r, q);
        theorem_order_transitive(b, r, q);
    }
}

/// `spec_in_unit_interval` means exactly what its name claims **in the
/// order**: a number between `0` and `1` inclusive.
///
/// The predicate has a component-wise definition (`0 <= n <= d`), and the order
/// has a cross-multiplied definition. This theorem states that the two
/// definitions agree. A caller can thus move between "the predicate holds" and
/// "`compare` against zero and one gives the same result". The `Number`
/// hypothesis on the right is necessary. No special value is in `[0, 1]`. `Nan`
/// is above `one` in the order, thus the order-based bounds alone do not
/// exclude it without the class test.
pub proof fn theorem_unit_interval_agrees_with_order(q: Q)
    requires
        q.wf(),
    ensures
        q.spec_in_unit_interval() <==> (q.spec_is_number() && Q::spec_le(
            Q::Number(Rat { num: 0, den: 1 }),
            q,
        ) && Q::spec_le(q, Q::Number(Rat { num: 1, den: 1 }))),
{
}

/// **Zero and one have exactly one representation each**, and the value
/// predicates recognise precisely it: `spec_is_zero` holds only of
/// `Number(0/1)` and `spec_is_one` only of `Number(1/1)`.
///
/// Neither direction is a definition unfold. `spec_is_zero` constrains the
/// numerator only, and the invariant clause `num == 0 ==> den == 1` fixes the
/// denominator. `spec_is_one` states `n == d`, and `gcd(n, n) == n` with the
/// coprimality invariant forces `n == d == 1`. This theorem is the enum-level
/// form of kernel canonicality. An `is_zero` or `is_one` test is thus a test of
/// the full bit pattern, and `Hash` cannot separate two zeros.
pub proof fn theorem_zero_one_unique_repr(q: Q)
    requires
        q.wf(),
    ensures
        q.spec_is_zero() <==> q == Q::Number(Rat { num: 0, den: 1 }),
        q.spec_is_one() <==> q == Q::Number(Rat { num: 1, den: 1 }),
{
    match q {
        Q::Number(x) => {
            if x.n() == x.d() {
                // n == d > 0, so gcd_int(n, d) == gcd_nat(nn, nn) with nn > 0.
                let nn = x.n() as nat;
                assert(crate::model::abs_int(x.n()) == x.n());
                // One definitional unfold: gcd(nn, nn) == gcd(nn, nn % nn).
                assert(nn % nn == 0) by (nonlinear_arith)
                    requires
                        nn > 0,
                ;
                crate::gcd::lemma_gcd_zero(nn);
                assert(crate::model::gcd_nat(nn, nn) == nn);
                // wf says that gcd is 1, so n == d == 1.
                assert(x.n() == 1);
            }
        },
        _ => {},
    }
}

} // verus!

// ---------------------------------------------------------------------------
// Standard trait impls
//
// These implementations are total delegations to the verified functions above,
// in the pattern that `Rat` uses. Verus does not model the `core` comparison
// traits, thus these implementations are `external`. Verified code cannot call
// them and does not need them.
// ---------------------------------------------------------------------------

#[cfg_attr(verus_keep_ghost, verifier::external)]
impl PartialOrd for Q {
    fn partial_cmp(&self, other: &Q) -> Option<core::cmp::Ordering> {
        Some(<Q as Ord>::cmp(self, other))
    }
}

#[cfg_attr(verus_keep_ghost, verifier::external)]
impl Ord for Q {
    /// This implementation delegates to the verified [`Q::compare`], which is
    /// proven against the ghost order. It does not reimplement the ranking.
    ///
    /// Do not use this order for `min`, `max` or `clamp`. `Ord`-based selection
    /// gives `min(Nan, Number(5)) == Number(5)`. The true value can be
    /// anything, and that result asserts the value 5. IEEE 754 has settled this
    /// question: 754-2008 defined `minNum` and `maxNum`, which returned the
    /// non-NaN operand, and 754-2019 withdrew them in favour of the
    /// NaN-propagating `minimum` and `maximum`. `slice.iter().min()` is thus
    /// not equivalent to a fold of the NaN-propagating `Q::min`, and the two
    /// give different results by design.
    fn cmp(&self, other: &Q) -> core::cmp::Ordering {
        Q::compare(*self, *other).cmp(&0)
    }
}

// ---------------------------------------------------------------------------
// Operator traits
//
// These implementations are total delegations, in the pattern that `Rat` uses.
// Verus does not model the `core::ops` traits, thus these implementations are
// `external` and add no assumption to a proof.
//
// This type implements `Div`, and `Rat` does not. Division on `Rat` has the
// precondition `!b.is_zero()`, which an operator cannot express, thus `a / b`
// on `Rat` can panic. `Q::div` is total, thus each input to `a / b` gives a
// value.
// ---------------------------------------------------------------------------

#[cfg_attr(verus_keep_ghost, verifier::external)]
impl core::ops::Add for Q {
    type Output = Q;

    fn add(self, rhs: Q) -> Q {
        Q::add(self, rhs)
    }
}

#[cfg_attr(verus_keep_ghost, verifier::external)]
impl core::ops::Sub for Q {
    type Output = Q;

    fn sub(self, rhs: Q) -> Q {
        Q::sub(self, rhs)
    }
}

#[cfg_attr(verus_keep_ghost, verifier::external)]
impl core::ops::Mul for Q {
    type Output = Q;

    fn mul(self, rhs: Q) -> Q {
        Q::mul(self, rhs)
    }
}

/// Total division. The note above states why this operator exists here and not
/// on `Rat`.
#[cfg_attr(verus_keep_ghost, verifier::external)]
impl core::ops::Div for Q {
    type Output = Q;

    fn div(self, rhs: Q) -> Q {
        Q::div(self, rhs)
    }
}

#[cfg_attr(verus_keep_ghost, verifier::external)]
impl core::ops::Neg for Q {
    type Output = Q;

    fn neg(self) -> Q {
        Q::neg(self)
    }
}

/// `Q::zero()` — the additive identity, and the identity `Sum` folds from.
#[cfg_attr(verus_keep_ghost, verifier::external)]
impl Default for Q {
    fn default() -> Q {
        Q::zero()
    }
}
