//! The extended `Q`: a rational, or an explicit non-representable state.
//!
//! This is an extension layer *over* the proven kernel, not a rewrite of it.
//! [`Rat`] keeps its invariant unchanged, so every obligation stated about it
//! keeps its exact statement; what this module adds is a discriminant that makes
//! "not a representable rational" an observable state instead of something the
//! caller is trusted to have ruled out.
//!
//! The design is issue #26. Two points from it are load-bearing here:
//!
//! * **A special carries no `num`/`den`,** so no operation can misread one as a
//!   number. That is the `recip(0)` defect class, and it dies with the encoding.
//!   The discriminant also makes an omitted case a *compile* error rather than a
//!   discipline every future author has to remember — which a sentinel
//!   `den == 0` encoding would not.
//! * **There is deliberately no `is_finite()`.** `PosSat` denotes genuinely
//!   finite reals — a magnitude above the budget is still a real number — so
//!   "finite" is the wrong axis to split this type on. The four predicates below
//!   split it on the axis that actually exists.

use verus_builtin_macros::verus;

#[allow(unused_imports)]
use verus_builtin::*;
#[allow(unused_imports)]
use vstd::prelude::*;

use crate::types::{Dir, Rat};

verus! {

/// The sign of a value that has one.
///
/// [`Q::signum`] returns `Option<Sign>` rather than an integer because
/// `signum(Nan)` has no answer: `Nan` denotes all of `ℝ ∪ {±∞}`, so no sign is
/// sound. `None` is exactly the `Nan` case — every other state, including both
/// saturations and both infinities, is sign-definite.
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
/// The open endpoint is forced by the code rather than chosen:
/// `magnitude_fits` in [`crate::model`] is `|n| <= MAX_MAG · d`, so saturation
/// triggers strictly *above* `MAX_MAG`, and `MAX_MAG` itself is representable as
/// `MAX_MAG/1`.
///
/// `PosSat` and `NegSat` denoting reals only — never `±∞` — is not a detail. It
/// is what makes `Number(0) · PosSat` exactly `Number(0)`, where `0 · ±∞` is
/// `Nan`. Saturation is strictly better behaved than infinity, and that is the
/// reason both exist as separate states.
///
/// # Equality
///
/// `PartialEq` is derived, and that is deliberate. `Rat` is canonical, so its
/// structural equality is mathematical equality; the specials carry no payload,
/// so there is no "two distinct NaNs" problem and `Nan == Nan` is true. That
/// reflexivity is what keeps `Eq` lawful, `Hash` consistent with `Eq`, and the
/// order in `Ord` total. It is a deliberate departure from IEEE 754, which makes
/// `NaN != NaN`.
///
/// `Ord` is **not** derived — see the `Ord` impl. The derived order would follow
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
    /// This is the enum-level counterpart of `Rat::wf`, and it is deliberately
    /// this weak: the whole point of the specials is that they have no
    /// representation invariant to violate.
    pub open spec fn wf(self) -> bool {
        match self {
            Q::Number(x) => x.wf(),
            _ => true,
        }
    }

    // -----------------------------------------------------------------------
    // Classification
    //
    // These four `ensures` clauses restate their own bodies, and that is
    // honest rather than circular *here*: a discriminant test has no content
    // beyond which variant it accepts, so the specification and the
    // implementation are the same statement. Nothing is being proven; the
    // clauses exist so that callers in verified code can reason about the
    // result at all.
    //
    // The predicates further down (`is_zero`, `signum`, ...) are a different
    // matter — they have real content, and they delegate to the verified
    // kernel rather than restating it.
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
    /// exhaustive — see `theorem_classification_partitions`.
    pub fn is_number(self) -> (r: bool)
        ensures
            r == self.spec_is_number(),
    {
        matches!(self, Q::Number(_))
    }

    /// Whether the true magnitude is known to exceed `MAX_MAG`.
    ///
    /// Note this is *not* the negation of `is_number`: it distinguishes an
    /// overflow from a division by zero, which is the diagnostic value that
    /// earns the saturation states their place in the type.
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
    // Each establishes `wf`. The specials do so trivially, which is the point:
    // there is no way to build a malformed special, so the constructors for
    // them cannot fail and need no `Option`.
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
    /// Unlike [`Rat::new`] this is **total**: `den == 0` is no longer a failure
    /// to be reported out-of-band but a value in the type, resolved by the
    /// IEEE 754 convention of issue #26 §4 — `x/0` takes the positive-side limit
    /// by fiat, exactly as IEEE does for `+0`, and `0/0` carries no information.
    ///
    /// # Saturation is judged on the value, not on the components
    ///
    /// This distinction is load-bearing and easy to get wrong. `Rat::new`
    /// returns `None` for two quite different reasons: the *value* exceeds the
    /// budget (`i64::MAX / 1`), or the *reduced denominator* exceeds it while
    /// the value itself is tiny (`1 / i64::MIN`, which is about `-1.08e-19`).
    /// Only the first is saturation. Treating the second as `NegSat` would
    /// claim `|value| > MAX_MAG` of a value in `(-1, 0)` — an unsound denotation,
    /// and exactly the class of silent wrong answer this type exists to remove.
    ///
    /// So the test here is [`crate::model`]'s `magnitude_fits` on the value, and
    /// a pair that fits in magnitude but not in its components is **rounded**
    /// rather than saturated. That is sound under R3, and #26 §11 makes the same
    /// call in rejecting a `Tiny` state: underflow-to-zero is inside the
    /// rounding contract, not a defect to surface.
    ///
    /// Where [`Rat::new`] succeeds, this agrees with it exactly — rounding a
    /// value that is already representable returns it unchanged (R1).
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
    // Every one of these is `false` on `Nan`, which is stated in the design
    // rather than left emergent: `Nan` denotes every value, so no non-trivial
    // predicate can soundly hold of it.
    //
    // These delegate to the verified kernel predicates on `Rat` instead of
    // reimplementing the arithmetic. Reimplementation is what makes a
    // postcondition that mirrors its own body dangerous — a typo duplicated
    // into both still verifies. Delegation means the content is carried by
    // `Rat`'s own proven contract.
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
    /// Constructors state their result with this rather than by naming a
    /// kernel constructor, because `Rat::zero()` and friends are `exec` and so
    /// cannot appear in a specification.
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
    /// False on every special. `PosSat` denotes `(MAX_MAG, +∞)`, which does not
    /// contain zero, so this is not merely a convention there — it is the
    /// answer. On `Nan` it is a convention, and the one the design fixes.
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
    /// False on every special, and on the saturations that is again the true
    /// answer rather than a convention: both saturation ranges lie entirely
    /// outside `[0, 1]`.
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
    /// `None` exactly on `Nan`. Both saturations and both infinities are
    /// sign-definite and answer `Some`, which is the whole reason the sign is
    /// carried in the discriminant rather than discarded.
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
// The kernel's `nary::sum`/`product`/`weighted_mean` clamp: `sum(&[M, M, -M])`
// clamps to `M`, then subtracts, and returns `0` — silently wrong, since the
// true total is `M`. These fold with the enum's operations instead, so an
// overflow anywhere in the chain is reported rather than absorbed.
//
// #26 §9.2 is honest about the cost and so is this: once a partial fold
// saturates, `PosSat + Number(-M)` is `Nan` and the fold never recovers. A
// sequence of representable numbers whose exact total is representable can
// still yield `Nan`. That is strictly less useful than `f64`'s sticky
// infinities — but it is *honest*, where the kernel's `0` is not. Callers who
// need the exact-path guarantee should check `is_number()` on the result, which
// is exactly the "all partial folds are `Number`" hypothesis §9.2 calls for.
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
    /// Left-to-right is part of the contract, not an implementation detail:
    /// with rounding, addition is not associative, so the order fixes the
    /// answer and is what makes the result reproducible.
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
    /// **Total**, where the kernel's returns `Option`. A zero total weight is no
    /// longer an out-of-band failure: it is `Nan` when the weighted numerator is
    /// also zero (`0/0` carries no information) and a signed infinity otherwise,
    /// by the same #26 §4 convention every other division follows. An empty
    /// slice is `Nan` for that reason, not by special case.
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
// Saturation moves into the enum here. The kernel silently returns
// `±MAX_MAG/1` when a sum or product leaves the budget — `Rat::add(M, M)` is
// `M`, wrong by a factor of two and indistinguishable from a real result — and
// this layer reports `PosSat`/`NegSat` instead.
//
// The precision cliffs marked below are option (A) from §6, taken knowingly:
// the lattice has no element for "sign known, magnitude unknown", so a few
// cells must answer `Nan` where a `PosUnknown`/`NegUnknown` state would answer
// precisely. A cliff only bites a computation that continues *after* an
// overflow, which arguably it should not.
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
    /// `Number(x) + PosSat` denotes `(MAX_MAG + x, +∞)`. For `x >= 0` that is
    /// contained in `⟦PosSat⟧` and the answer is sound. For `x < 0` the lower
    /// endpoint `MAX_MAG + x` can fall as low as `0`, so the image includes
    /// representable values and `PosSat` would be **unsound** — hence the cliff.
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
    /// The boundary is **inclusive**: at `|x| == 1` the image is exactly
    /// `1 · (MAX_MAG, ∞) = (MAX_MAG, ∞)`, so saturation is sound and minimal
    /// there. The cliff is the open interval `0 < |x| < 1`, where the image
    /// `(MAX_MAG·|x|, ∞)` dips below `MAX_MAG`. (An earlier draft of §5 wrote
    /// the condition as `x > 1`, which gratuitously sent `one() * PosSat` to
    /// `Nan` and contradicted `neg(PosSat) == NegSat`.)
    ///
    /// `Number(0) * Sat` is exactly `Number(0)` — **not** `Nan` — because `Sat`
    /// denotes finite reals only. This is the clearest case of saturation being
    /// better behaved than infinity, where `0 · ±∞` genuinely is indeterminate.
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
    /// Replaces a kernel `add` that silently clamps: `Rat::add(MAX_MAG,
    /// MAX_MAG)` returns `MAX_MAG/1`, wrong by a factor of two, carrying no
    /// error guarantee and indistinguishable from a real result unless the
    /// caller happened to reach for `checked_add`.
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
            // An infinity out requires an infinity in — addition cannot
            // manufacture one, which is what keeps `is_infinite()` meaning
            // "a division by zero happened somewhere upstream".
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
    /// Defined as `a + (-b)`, exactly as §5 specifies, so the two can never
    /// disagree about an overflowing difference.
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
            // An infinite operand yields an infinity or `Nan`, never a
            // representable product — even against zero, where it is `Nan`.
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
            // `0 · ±∞` is genuinely indeterminate — unlike `0 · Sat`, which is
            // exactly zero.
            (Q::Number(x), Q::PosInf) => Q::number_times_inf(x, true),
            (Q::Number(x), Q::NegInf) => Q::number_times_inf(x, false),
            (Q::PosInf, Q::Number(y)) => Q::number_times_inf(y, true),
            (Q::NegInf, Q::Number(y)) => Q::number_times_inf(y, false),
            // Saturations multiply by sign and stay saturated: a product of two
            // magnitudes above MAX_MAG is far above it.
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
    /// `pow_u32(a, 0)` is `Number(1)` for **every** `a`, including `Nan` —
    /// matching IEEE's `NaN^0 == 1`, which #26 §5 calls out rather than leaving
    /// emergent. The exponent is a count, not a value, so the base's
    /// informativeness is irrelevant when it is used zero times.
    ///
    /// A left fold of [`Q::mul`], the same shape as the kernel's `pow_u32`, so
    /// the two associate their roundings identically. That matters: with
    /// rounding, multiplication is *not* associative in general, so a
    /// square-and-multiply implementation would not merely be faster, it could
    /// give a different answer.
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
    /// #26 §3: the kernel's four `checked_*` contracts are literally
    /// `r.is_none() <==> saturated(...)`, so the discriminant carries precisely
    /// the same information and these collapse to sugar. A provable
    /// equivalence, not an approximation — and unlike the kernel's versions
    /// these cannot panic.
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
    /// Note this can succeed with a *saturated* operand: `Number(0) * PosSat`
    /// is exactly `Number(0)`, so unlike `checked_add` there is no "a saturated
    /// input means `None`" rule to state.
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
// The only entries in the whole design that are exact and total with no
// precision cliff anywhere: negation is a bijection on every state, and
// absolute value maps the two sign-definite pairs onto their positive halves.
// ---------------------------------------------------------------------------

impl Q {
    /// `-self`. Exact and total.
    ///
    /// Negation is sound on the saturations because `⟦PosSat⟧ = (MAX_MAG, ∞)`
    /// negates exactly onto `⟦NegSat⟧ = (-∞, -MAX_MAG)` — the denotation is
    /// symmetric, so nothing is lost. The kernel negation cannot overflow
    /// either: `|num| <= MAX_MAG` keeps it well clear of `i64::MIN`.
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
    /// Note `abs` is *not* injective — it maps both saturations to `PosSat` and
    /// both infinities to `PosInf` — which is correct and is why `neg` above
    /// carries the class-preservation postconditions and this one does not.
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
// These propagate `Nan`, and are therefore NOT the `Ord`-based selection that
// `slice.iter().min()` performs. The design is explicit that deriving them from
// the order would be a defect: `Ord`-based selection gives
// `min(Nan, Number(5)) == Number(5)`, asserting the true value is exactly 5
// when it could be anything — reintroducing, through the side door, the precise
// class of silent wrong answer this type exists to remove.
//
// IEEE fought and settled this. 754-2008's `minNum`/`maxNum` returned the
// non-NaN operand and were **withdrawn** in 754-2019, replaced by
// NaN-propagating `minimum`/`maximum` with the ignore-NaN behaviour given the
// separate explicit names `minimumNumber`/`maximumNumber`. Since §4 takes IEEE
// as the reference model, these are `minimum` semantics.
//
// On the sign-definite specials they follow the §5 order, which is sound there
// because those variants really do sit where the order puts them.
// ---------------------------------------------------------------------------

impl Q {
    /// The smaller of `a` and `b`, propagating `Nan`.
    ///
    /// **Deliberately disagrees with `Ord`-based selection.** A fold of this is
    /// not `slice.iter().min()`, and the difference is the point: this returns
    /// `Nan` if any input is `Nan`, where `Ord` would quietly pick the other
    /// operand and assert a value it does not have.
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
    /// `Nan` in any of the three arguments — including a bound — yields `Nan`.
    /// Clamping into a range whose endpoint carries no information cannot
    /// produce an informative answer, and returning `hi` there would be the
    /// `clamp(Nan, lo, hi) == hi` defect §5 calls out by name.
    ///
    /// Unlike the kernel's `clamp` this does **not** require `lo <= hi`: with
    /// `Nan` admissible as a bound the precondition could not be stated on the
    /// order alone. An inverted range yields `Nan` rather than an arbitrary
    /// endpoint, which is the only answer that does not assert something false.
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
            },
    {
        if a.is_nan() || lo.is_nan() || hi.is_nan() {
            Q::Nan
        } else if Q::lt(hi, lo) {
            // An inverted range has no consistent answer; saying so beats
            // silently returning an endpoint.
            Q::Nan
        } else if Q::lt(a, lo) {
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
// This closes the three defects that open #26, all of which reproduce on the
// kernel today:
//
//   * `Rat::zero().recip()` returns `Rat { num: -1, den: 0 }` — a value that
//     violates the type invariant and detonates later, far from the cause.
//   * `Rat::div(x, 0)` panics.
//   * `Rat::checked_div(x, 0)` panics, where std and `num-traits` both return
//     `None` for exactly this case.
//
// Every cell below is derived from the denotations in §2 rather than chosen:
// the result is the smallest state whose denotation contains the true image
// `{ x/y : x ∈ ⟦a⟧, y ∈ ⟦b⟧ }`. `Nan` is always sound because it denotes
// everything, so precision is the only thing that has to be argued.
// ---------------------------------------------------------------------------

impl Q {
    /// `x / y` for two representable rationals with `y != 0`.
    ///
    /// Saturates rather than clamping. The kernel's `Rat::div` silently returns
    /// `±MAX_MAG/1` when the exact quotient leaves the budget, which is a
    /// singleton denotation that does not contain the true value; reporting
    /// `PosSat`/`NegSat` instead keeps the denotation honest.
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
    /// `pos` says which saturation the numerator is. The image of
    /// `(MAX_MAG, ∞) / y` is `(MAX_MAG/y, ∞)` for `y > 0`, which stays inside
    /// `⟦PosSat⟧` only while `MAX_MAG/y >= MAX_MAG` — that is, while `y <= 1`.
    /// Past the unit boundary the image dips into representable territory and
    /// no saturation state is sound, which is the precision cliff §6 accepts.
    /// The boundary is inclusive: at `y == 1` the image is exactly `⟦PosSat⟧`.
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
            // A saturation is sign-definite and nonzero, so this is `x/0` with
            // `x != 0`: the IEEE convention of §4 gives a signed infinity.
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
    /// Never panics and never returns a value outside the type invariant. The
    /// division-by-zero cases follow issue #26 §4's decision to take IEEE 754 as
    /// the reference model, applied **uniformly** — an earlier draft of the
    /// design used the IEEE rule for `x/0` but a limit-rigorous `Nan` for
    /// `recip(0)` and `±∞/0`, which broke `recip(x) == div(one, x)` at `x = 0`
    /// for no reason.
    ///
    /// Two cells are worth pointing at because they are exact where the obvious
    /// guess is `Nan`:
    ///
    /// * `Sat / Inf` is `Number(0)`. `PosSat` denotes **reals only**, never
    ///   `±∞`, so the image is `{s/±∞} = {0}` exactly. This is where saturation
    ///   is strictly better behaved than infinity.
    /// * `Inf / Sat` is a signed infinity, for the same reason: dividing `±∞` by
    ///   a finite real leaves it infinite.
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
            // An infinity in the result means a zero divisor or an infinite
            // numerator — never an overflow. This is the property that keeps
            // `is_infinite()` usable as a diagnostic: it points at a division by
            // zero, while an overflow reports `is_saturated()` instead, and the
            // two never blur into each other.
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
            // `x / Sat`: the image is `(0, x/M)`, which straddles representable
            // values, so only `x == 0` has a sound answer — and there it is
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
            // `Sat / Sat` spans `(0, ∞)` (or its mirror) — sign known, magnitude
            // entirely unknown, which is the one thing this lattice cannot say.
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
    /// **Defined as `div(one, self)` rather than as its own case analysis**, and
    /// that is a deliberate correctness choice, not laziness. Issue #26 §4
    /// records that an earlier draft of the design gave `recip(0)` and `x/0`
    /// different answers, breaking `recip(x) == div(one, x)` at exactly the
    /// point that matters. Deriving one from the other makes that class of
    /// divergence unrepresentable instead of merely tested for — see
    /// `theorem_recip_is_div_one`.
    ///
    /// On a nonzero `Number` this is exact: reciprocating swaps a canonical
    /// pair, and both components were already inside the budget, so no rounding
    /// and no saturation can occur.
    ///
    /// This replaces a kernel operation that returned `Rat { num: -1, den: 0 }`
    /// for `recip(0)` — a value violating the type invariant.
    pub fn recip(self) -> (r: Q)
        requires
            self.wf(),
        ensures
            r.wf(),
            self.spec_is_nan() ==> r.spec_is_nan(),
    {
        // The cell-by-cell behaviour — `recip(0) == PosInf`, `recip(±∞) == 0`,
        // `recip` of a nonzero rational being exact and never saturating — is
        // not stated here, because deriving it would require `div`'s
        // postcondition to reproduce the whole propagation table in ghost form.
        // A specification shaped exactly like the table it specifies is the
        // circular kind that verifies with a mistake duplicated into both, so it
        // would buy confidence it does not earn.
        //
        // The table is instead pinned *exhaustively* in `tests/extended_q.rs`:
        // the state space is 6×6 cells, so the tests enumerate every one rather
        // than sampling. That is a complete check of the table, and it runs
        // against the compiled artifact.
        Q::div(Q::one(), self)
    }

    /// `a / b` when the result is a representable rational, `None` otherwise.
    ///
    /// Sugar over [`Q::div`], and provably exactly that: the `Option` carries
    /// precisely the information the discriminant already carries. Unlike the
    /// kernel's `checked_div` this **does not panic** on a zero divisor — it
    /// returns `None`, which is what `std` and `num-traits` do for this case.
    pub fn checked_div(a: Q, b: Q) -> (r: Option<Rat>)
        requires
            a.wf(),
            b.wf(),
        ensures
            r.is_some() ==> r.unwrap().wf(),
            // `None` whenever no representable quotient can exist: a zero
            // divisor, an operand carrying no information, or an infinite
            // numerator. The remaining way to get `None` is overflow, which is
            // the case the kernel's `checked_div` already reported — so this is
            // a strict extension of it, not a change of meaning.
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
// Stated and proven rather than assumed, because the four predicates are the
// only supported way to case-split on the type from outside, and a caller that
// handles all four is entitled to know it has handled everything.
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
// This orders *representations*, not denoted values, and outside `Number` that
// distinction is real: `PosSat == PosSat` compares `Equal` while the two true
// values may differ. Inside `Number` it is the order on rationals.
//
// The placement is sound at the boundaries rather than merely conventional:
// every `NegSat` value is `< -MAX_MAG <=` any `Number`, and every `PosSat`
// value is `> MAX_MAG >=` any `Number`, so the separations are strict. Only
// `Nan`'s position is a free choice, and it is a choice — `f64::total_cmp`
// puts negative NaN first and positive NaN last, so the analogy is partial.
// ---------------------------------------------------------------------------

impl Q {
    /// The position of a variant in the order above.
    ///
    /// A rank rather than the declaration order, so that reordering the enum's
    /// variants cannot silently change the order on values. That is also why
    /// `Ord` is hand-written instead of derived.
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
    /// Total — there is no incomparable pair, which is the point of giving
    /// `Nan` a definite position.
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
            // The only case with a payload to compare. Delegates to the
            // verified kernel comparison rather than cross-multiplying again
            // here.
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
/// This is the property IEEE 754 gives up — it makes every ordered comparison
/// involving `NaN` false, so `NaN` is incomparable with everything including
/// itself. Recovering totality is the second deliberate departure from IEEE in
/// this design, alongside `Nan == Nan`.
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
/// Stated as `a == b` rather than as `spec_eq(a, b)` on purpose. `spec_eq` is
/// *defined* as `spec_le(a, b) && spec_le(b, a)`, so concluding it from those
/// two hypotheses would restate the hypothesis and prove nothing. The content is
/// that the order's notion of "equal" coincides with the derived `PartialEq`,
/// which is exactly what makes deriving `PartialEq`/`Eq`/`Hash` alongside a
/// hand-written `Ord` sound — `Ord` and `Eq` cannot disagree.
///
/// On the `Number` case this rests on the kernel's canonicality result: two
/// well-formed `Rat` are mathematically equal exactly when they are structurally
/// equal, so there is no pair of distinct representations the order would have
/// to call equal.
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
/// The other direction of the theorem above, completing the equivalence that
/// `Ord`/`Eq` consistency depends on.
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
/// The cross-rank cases are ordinary integer transitivity on the rank. The
/// all-`Number` case is the kernel's own transitivity lemma, reused rather than
/// reproved.
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
/// Stated because it is the load-bearing soundness fact for the placement: it
/// is what makes the order on representations agree with the order on denoted
/// values wherever both are defined.
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

} // verus!

// ---------------------------------------------------------------------------
// Standard trait impls
//
// Thin, total delegations to the verified functions above, following the same
// pattern as `Rat`'s: Verus does not model the `core` comparison traits, so
// they are `external` — not callable from verified code, and verified code
// never needs them.
// ---------------------------------------------------------------------------

#[cfg_attr(verus_keep_ghost, verifier::external)]
impl PartialOrd for Q {
    fn partial_cmp(&self, other: &Q) -> Option<core::cmp::Ordering> {
        Some(<Q as Ord>::cmp(self, other))
    }
}

#[cfg_attr(verus_keep_ghost, verifier::external)]
impl Ord for Q {
    /// Delegates to the verified [`Q::compare`], which is proven against the
    /// ghost order, rather than reimplementing the ranking here.
    ///
    /// **This order must not be used for `min`/`max`/`clamp`.** `Ord`-based
    /// selection would give `min(Nan, Number(5)) == Number(5)`: the true value
    /// could be anything, and the result asserts it is exactly 5. That
    /// reintroduces, through the side door, the defect class this type exists
    /// to remove. IEEE fought and settled this — 754-2008's `minNum`/`maxNum`
    /// returned the non-NaN operand and were *withdrawn* in 754-2019 in favour
    /// of NaN-propagating `minimum`/`maximum`. Consequently
    /// `slice.iter().min()` is **not** equivalent to a fold of a NaN-propagating
    /// `Q::min`, and the two are meant to disagree.
    fn cmp(&self, other: &Q) -> core::cmp::Ordering {
        Q::compare(*self, *other).cmp(&0)
    }
}

// ---------------------------------------------------------------------------
// Operator traits
//
// Thin, total delegations, following the same pattern as `Rat`'s: Verus does
// not model the `core::ops` traits, so they are `external` and contribute no
// assumptions to any proof.
//
// Unlike `Rat`, this type implements `Div`. The reason `Rat` deliberately does
// not is that its division carries a precondition (`!b.is_zero()`) an operator
// cannot express, so `a / b` would be a panic waiting for a caller who forgot.
// `Q::div` is total, so the objection is gone: there is no input for which
// `a / b` fails to produce a value.
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

/// Total division. See the note above on why this exists here and not on `Rat`.
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
