//! The extended [`Q`]: a `Rat`, or an explicit non-representable state.
//!
//! A layer over the kernel, not a rewrite: `Rat` keeps its invariant and every
//! kernel obligation keeps its statement. Special values carry no `num`/`den`,
//! so no operation can read one as a number and an omitted case is a compile
//! error. There is no `is_finite()`: `PosSat` denotes finite reals above the
//! budget. Issue #26 holds the design and the propagation tables, which
//! `tests/extended_q.rs` pins by exhaustive enumeration.

use verus_builtin_macros::verus;

#[allow(unused_imports)]
use verus_builtin::*;
#[allow(unused_imports)]
use vstd::prelude::*;

use crate::types::{Dir, Rat};

verus! {

/// The sign of a value that has one; `signum(Nan)` is `None`.
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
/// | variant | denotes |
/// |---|---|
/// | `Number(x)` | `{x}` |
/// | `PosSat` / `NegSat` | `(MAX_MAG, +∞)` / `(-∞, -MAX_MAG)`, reals only |
/// | `PosInf` / `NegInf` | `{+∞}` / `{-∞}` |
/// | `Nan` | no information |
///
/// Saturation denotes reals, so `Number(0) · PosSat == Number(0)`. `PartialEq`
/// is derived and `Nan == Nan`, which keeps `Eq`, `Hash` and the total `Ord`
/// lawful. `Ord` is hand-written: variant order is not value order.
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
    /// The invariant: a `Number` payload is `wf`; specials carry nothing.
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

    /// The sign of this value in specifications. `Nan` is the only state with
    /// no sound sign.
    pub open spec fn spec_signum(self) -> Option<Sign> {
        match self {
            Q::Number(x) => {
                if x.n() < 0 {
                    Some(Sign::Negative)
                } else if x.n() > 0 {
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

    /// Whether this is a representable rational.
    ///
    /// The four classification predicates are mutually exclusive and jointly
    /// exhaustive. See `theorem_classification_partitions`.
    ///
    /// ```
    /// use the_q::{Q, Rat};
    ///
    /// assert!(Q::number(Rat::one()).is_number());
    /// assert!(!Q::PosSat.is_number());
    /// assert!(!Q::Nan.is_number());
    /// ```
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
    ///
    /// ```
    /// use the_q::Q;
    ///
    /// assert!(Q::PosSat.is_saturated());
    /// assert!(Q::NegSat.is_saturated());
    /// assert!(!Q::PosInf.is_saturated());
    /// ```
    pub fn is_saturated(self) -> (r: bool)
        ensures
            r == self.spec_is_saturated(),
    {
        matches!(self, Q::PosSat | Q::NegSat)
    }

    /// Whether this is exactly `±∞`.
    ///
    /// ```
    /// use the_q::Q;
    ///
    /// assert!(Q::PosInf.is_infinite());
    /// assert!(Q::NegInf.is_infinite());
    /// assert!(!Q::PosSat.is_infinite());
    /// ```
    pub fn is_infinite(self) -> (r: bool)
        ensures
            r == self.spec_is_infinite(),
    {
        matches!(self, Q::PosInf | Q::NegInf)
    }

    /// Whether this carries no information about the value.
    ///
    /// ```
    /// use the_q::Q;
    ///
    /// assert!(Q::Nan.is_nan());
    /// assert!(!Q::zero().is_nan());
    /// ```
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
    ///
    /// ```
    /// use the_q::{Q, Rat};
    ///
    /// let half = Rat::new(1, 2).unwrap();
    /// assert_eq!(Q::number(half), Q::Number(half));
    /// ```
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
    ///
    /// ```
    /// use the_q::Q;
    ///
    /// assert!(Q::zero().is_zero());
    /// assert!(Q::zero().is_number());
    /// ```
    pub fn zero() -> (r: Q)
        ensures
            r.wf(),
            r.spec_is_number(),
            r.spec_is_value(0, 1),
            r.spec_is_zero(),
            r == Q::Number(Rat::from_raw_spec(0, 1)),
    {
        Q::Number(Rat::zero())
    }

    /// `1`.
    ///
    /// ```
    /// use the_q::Q;
    ///
    /// assert!(Q::one().is_one());
    /// ```
    pub fn one() -> (r: Q)
        ensures
            r.wf(),
            r.spec_is_number(),
            r.spec_is_value(1, 1),
            r.spec_is_one(),
            r == Q::Number(Rat::from_raw_spec(1, 1)),
    {
        Q::Number(Rat::one())
    }

    /// `-1`.
    ///
    /// ```
    /// use the_q::{Q, Rat};
    ///
    /// assert_eq!(Q::neg_one(), Q::Number(Rat::new(-1, 1).unwrap()));
    /// ```
    pub fn neg_one() -> (r: Q)
        ensures
            r.wf(),
            r.spec_is_number(),
            r.spec_is_value(-1, 1),
    {
        Q::Number(Rat::neg_one())
    }

    /// The rational `num / den`, total: `x/0` is `±Inf`, `0/0` is `Nan`.
    /// Saturation is decided on the *value* (`magnitude_fits`), not on the
    /// components: `1 / i64::MIN` is small and rounds, it does not saturate.
    /// Where [`Rat::new`] succeeds this returns the same value.
    ///
    /// ```
    /// use the_q::{Q, Rat};
    ///
    /// assert_eq!(Q::new(1, 2), Q::Number(Rat::new(1, 2).unwrap()));
    /// assert_eq!(Q::new(1, 0), Q::PosInf);
    /// assert_eq!(Q::new(0, 0), Q::Nan);
    /// ```
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
    // Delegate to the kernel predicates: a reimplementation would mirror its own
    // postcondition and verify with a shared defect.

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
    ///
    /// ```
    /// use the_q::Q;
    ///
    /// assert!(Q::zero().is_zero());
    /// assert!(!Q::PosSat.is_zero());
    /// assert!(!Q::Nan.is_zero());
    /// ```
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
    ///
    /// ```
    /// use the_q::Q;
    ///
    /// assert!(Q::one().is_one());
    /// assert!(!Q::PosSat.is_one());
    /// ```
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
    ///
    /// ```
    /// use the_q::{Q, Rat};
    ///
    /// assert!(Q::number(Rat::new(1, 2).unwrap()).in_unit_interval());
    /// assert!(!Q::PosSat.in_unit_interval());
    /// ```
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
    ///
    /// ```
    /// use the_q::{Q, Sign};
    ///
    /// assert_eq!(Q::one().signum(), Some(Sign::Positive));
    /// assert_eq!(Q::zero().signum(), Some(Sign::Zero));
    /// assert_eq!(Q::PosSat.signum(), Some(Sign::Positive));
    /// assert_eq!(Q::Nan.signum(), None);
    /// ```
    pub fn signum(self) -> (r: Option<Sign>)
        requires
            self.wf(),
        ensures
            r == self.spec_signum(),
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

/// The sign classification is total away from `Nan`, and zero is recognized
/// exactly rather than merely implied in one direction.
pub proof fn theorem_signum_complete(q: Q)
    requires
        q.wf(),
    ensures
        (q.spec_signum() == Some(Sign::Zero)) <==> q.spec_is_zero(),
        q.spec_signum().is_none() <==> q.spec_is_nan(),
        !(q.spec_signum() == Some(Sign::Positive)
            && q.spec_signum() == Some(Sign::Negative)),
{
    match q {
        Q::Number(x) => {
            if x.n() < 0 {
            } else if x.n() > 0 {
            } else {
            }
        },
        _ => {},
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
// After a partial fold saturates, `PosSat + Number(-M)` is `Nan` and the fold
// does not recover; check `is_number()` on the result for the exact-path
// guarantee.

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
    ///
    /// ```
    /// use the_q::Q;
    ///
    /// let xs = [Q::one(), Q::one(), Q::one()];
    /// assert_eq!(Q::sum(&xs), Q::number(the_q::Rat::new(3, 1).unwrap()));
    /// assert!(Q::sum(&[]).is_zero());
    /// ```
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
    ///
    /// ```
    /// use the_q::{Q, Rat};
    ///
    /// let xs = [Q::number(Rat::new(2, 1).unwrap()), Q::number(Rat::new(3, 1).unwrap())];
    /// assert_eq!(Q::product(&xs), Q::number(Rat::new(6, 1).unwrap()));
    /// assert!(Q::product(&[]).is_one());
    /// ```
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

    /// `sum(w_i · x_i) / sum(w_i)`, total: a zero weight sum gives `Nan` (`0/0`)
    /// or a signed infinity, and an empty slice gives `Nan` the same way.
    ///
    /// ```
    /// use the_q::{Q, Rat};
    ///
    /// let one = Q::one();
    /// let two = Q::number(Rat::new(2, 1).unwrap());
    /// // weight 1 on `1`, weight 3 on `2`: (1*1 + 3*2) / (1 + 3) == 7/4
    /// let three = Q::number(Rat::new(3, 1).unwrap());
    /// let pairs = [(one, one), (three, two)];
    /// assert_eq!(Q::weighted_mean(&pairs), Q::number(Rat::new(7, 4).unwrap()));
    /// assert!(Q::weighted_mean(&[]).is_nan());
    /// ```
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
    /// Ghost mirror of [`Q::add_numbers`]. Exists only so `Q::add`'s result is
    /// *nameable* in ghost code, the same role `round_frac` plays for
    /// `round_frac_exec` (V4): it lets `add`'s `ensures` pin `r ==
    /// Q::spec_add(a, b)`, which is what makes the algebraic-law theorems in
    /// `laws_q.rs` statable at all.
    ///
    /// This is *not* the specification of soundness. It is shaped like the
    /// implementation on purpose, because its only job is to *equal* the
    /// implementation. `denote.rs`'s `denotes`/`add_sound`/`add_honest` are
    /// the specification, and by construction they never call this function
    /// (checked by `scripts/check-no-spec-mirror-in-denote.sh`) — a spec
    /// shaped like the table it specifies verifies with a shared mistake
    /// (the scar this crate already carries once, noted at `recip` below).
    pub open spec fn spec_add_numbers(x: Rat, y: Rat) -> Q {
        let n = crate::q::add_n(x, y);
        let d = crate::q::prod_d(x, y);
        if crate::model::magnitude_fits(n, d) {
            Q::Number(crate::round::round_frac(n, d, Dir::Nearest))
        } else if n > 0 {
            Q::PosSat
        } else {
            Q::NegSat
        }
    }

    /// `x + y` for two representable rationals, saturating rather than clamping.
    fn add_numbers(x: Rat, y: Rat) -> (r: Q)
        requires
            x.wf(),
            y.wf(),
        ensures
            r.wf(),
            !r.spec_is_nan(),
            !r.spec_is_infinite(),
            r == Q::spec_add_numbers(x, y),
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

    /// Ghost mirror of [`Q::mul_numbers`]. See [`Q::spec_add_numbers`].
    pub open spec fn spec_mul_numbers(x: Rat, y: Rat) -> Q {
        let n = crate::q::mul_n(x, y);
        let d = crate::q::prod_d(x, y);
        if crate::model::magnitude_fits(n, d) {
            Q::Number(crate::round::round_frac(n, d, Dir::Nearest))
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
            r == Q::spec_mul_numbers(x, y),
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

    /// Ghost mirror of [`Q::number_plus_sat`]. See [`Q::spec_add_numbers`].
    pub open spec fn spec_number_plus_sat(x: Rat, sat_pos: bool) -> Q {
        if sat_pos {
            if x.n() >= 0 {
                Q::PosSat
            } else {
                Q::Nan
            }
        } else {
            if x.n() <= 0 {
                Q::NegSat
            } else {
                Q::Nan
            }
        }
    }

    /// `Number(x) + Sat`: sound for `x` on the saturation's side; for the other
    /// sign the image reaches inside the budget and the result is `Nan`.
    fn number_plus_sat(x: Rat, sat_pos: bool) -> (r: Q)
        requires
            x.wf(),
        ensures
            r.wf(),
            !r.spec_is_infinite(),
            !r.spec_is_number(),
            r == Q::spec_number_plus_sat(x, sat_pos),
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

    /// `Number(x) * Sat`. Saturated for `|x| >= 1` (inclusive: `one() * PosSat`
    /// must stay `PosSat`), `Nan` for `0 < |x| < 1` where the image reaches
    /// below `MAX_MAG`, and exactly `Number(0)` at zero.
    /// Ghost mirror of [`Q::number_times_sat`]. See [`Q::spec_add_numbers`].
    pub open spec fn spec_number_times_sat(x: Rat, sat_pos: bool) -> Q {
        if x.n() == 0 {
            Q::Number(Rat::from_raw_spec(0, 1))
        } else if !(x.n() >= x.d() || x.n() <= 0 - x.d()) {
            Q::Nan
        } else if (x.n() > 0) == sat_pos {
            Q::PosSat
        } else {
            Q::NegSat
        }
    }

    fn number_times_sat(x: Rat, sat_pos: bool) -> (r: Q)
        requires
            x.wf(),
        ensures
            r.wf(),
            !r.spec_is_infinite(),
            r == Q::spec_number_times_sat(x, sat_pos),
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

    /// Ghost mirror of [`Q::add`]'s match, cell for cell. This is *not* the
    /// specification of `add`'s correctness — `denote.rs`'s
    /// `add_sound`/`add_honest`/`add_nan_is_necessary` are, and none of them
    /// call this function. Its only job is to make `add`'s result nameable in
    /// ghost code (`r == Q::spec_add(a, b)`), which is the prerequisite the
    /// commutativity/associativity/distributivity/monotonicity theorems in
    /// `laws_q.rs` need: none of those properties are even statable against a
    /// return value that only classification `ensures` clauses constrain.
    pub open spec fn spec_add(a: Q, b: Q) -> Q {
        match (a, b) {
            (Q::Nan, _) => Q::Nan,
            (_, Q::Nan) => Q::Nan,
            (Q::Number(x), Q::Number(y)) => Q::spec_add_numbers(x, y),
            (Q::Number(x), Q::PosSat) => Q::spec_number_plus_sat(x, true),
            (Q::Number(x), Q::NegSat) => Q::spec_number_plus_sat(x, false),
            (Q::PosSat, Q::Number(y)) => Q::spec_number_plus_sat(y, true),
            (Q::NegSat, Q::Number(y)) => Q::spec_number_plus_sat(y, false),
            (Q::PosSat, Q::PosSat) => Q::PosSat,
            (Q::NegSat, Q::NegSat) => Q::NegSat,
            (Q::PosSat, Q::NegSat) => Q::Nan,
            (Q::NegSat, Q::PosSat) => Q::Nan,
            (Q::PosInf, Q::NegInf) => Q::Nan,
            (Q::NegInf, Q::PosInf) => Q::Nan,
            (Q::PosInf, _) => Q::PosInf,
            (Q::NegInf, _) => Q::NegInf,
            (_, Q::PosInf) => Q::PosInf,
            (_, Q::NegInf) => Q::NegInf,
        }
    }

    /// `a + b`, total. Replaces the kernel `add`, which clamps silently.
    ///
    /// ```
    /// use the_q::{Q, Rat, MAX_MAG};
    ///
    /// assert_eq!(Q::add(Q::one(), Q::one()), Q::number(Rat::new(2, 1).unwrap()));
    /// // Two representable rationals overflowing the budget saturate, they do
    /// // not become infinite.
    /// let m = Q::number(Rat::new(MAX_MAG, 1).unwrap());
    /// assert_eq!(Q::add(m, m), Q::PosSat);
    /// assert!(Q::add(Q::Nan, Q::one()).is_nan());
    /// ```
    pub fn add(a: Q, b: Q) -> (r: Q)
        requires
            a.wf(),
            b.wf(),
        ensures
            r.wf(),
            r == Q::spec_add(a, b),
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
    ///
    /// ```
    /// use the_q::{Q, Rat};
    ///
    /// assert_eq!(Q::sub(Q::one(), Q::one()), Q::zero());
    /// assert!(Q::sub(Q::Nan, Q::zero()).is_nan());
    /// ```
    pub fn sub(a: Q, b: Q) -> (r: Q)
        requires
            a.wf(),
            b.wf(),
        ensures
            r.wf(),
            r == Q::spec_add(a, Q::spec_neg(b)),
            a.spec_is_nan() ==> r.spec_is_nan(),
            b.spec_is_nan() ==> r.spec_is_nan(),
    {
        Q::add(a, b.neg())
    }

    /// Ghost mirror of [`Q::mul`]'s match. See [`Q::spec_add`].
    pub open spec fn spec_mul(a: Q, b: Q) -> Q {
        match (a, b) {
            (Q::Nan, _) => Q::Nan,
            (_, Q::Nan) => Q::Nan,
            (Q::Number(x), Q::Number(y)) => Q::spec_mul_numbers(x, y),
            (Q::Number(x), Q::PosSat) => Q::spec_number_times_sat(x, true),
            (Q::Number(x), Q::NegSat) => Q::spec_number_times_sat(x, false),
            (Q::PosSat, Q::Number(y)) => Q::spec_number_times_sat(y, true),
            (Q::NegSat, Q::Number(y)) => Q::spec_number_times_sat(y, false),
            (Q::Number(x), Q::PosInf) => Q::spec_number_times_inf(x, true),
            (Q::Number(x), Q::NegInf) => Q::spec_number_times_inf(x, false),
            (Q::PosInf, Q::Number(y)) => Q::spec_number_times_inf(y, true),
            (Q::NegInf, Q::Number(y)) => Q::spec_number_times_inf(y, false),
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

    /// `a * b`, total.
    ///
    /// ```
    /// use the_q::Q;
    ///
    /// // Saturation denotes a finite real, so zero times it is exactly zero...
    /// assert_eq!(Q::mul(Q::zero(), Q::PosSat), Q::zero());
    /// // ...but zero times a true infinity is the classic indeterminate.
    /// assert!(Q::mul(Q::zero(), Q::PosInf).is_nan());
    /// ```
    pub fn mul(a: Q, b: Q) -> (r: Q)
        requires
            a.wf(),
            b.wf(),
        ensures
            r.wf(),
            r == Q::spec_mul(a, b),
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

    /// `self^e`, total. `pow_u32(a, 0)` is `1` for every `a` including `Nan`, as
    /// IEEE `NaN^0`. A left fold of [`Q::mul`], associating like the kernel.
    ///
    /// ```
    /// use the_q::{Q, Rat};
    ///
    /// let two = Q::number(Rat::new(2, 1).unwrap());
    /// assert_eq!(two.pow_u32(3), Q::number(Rat::new(8, 1).unwrap()));
    /// assert!(Q::Nan.pow_u32(0).is_one());
    /// ```
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

    /// `a + b` as a `Rat`, `None` otherwise. A view over [`Q::add`]; cannot panic.
    ///
    /// ```
    /// use the_q::{Q, Rat};
    ///
    /// assert_eq!(Q::checked_add(Q::one(), Q::one()), Some(Rat::new(2, 1).unwrap()));
    /// assert_eq!(Q::checked_add(Q::PosInf, Q::one()), None);
    /// ```
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
    ///
    /// ```
    /// use the_q::{Q, Rat};
    ///
    /// assert_eq!(Q::checked_sub(Q::one(), Q::one()), Some(Rat::zero()));
    /// assert_eq!(Q::checked_sub(Q::Nan, Q::one()), None);
    /// ```
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

    /// `a * b` as a `Rat`, `None` otherwise. Can succeed on a saturated operand:
    /// `Number(0) * PosSat` is `0`.
    ///
    /// ```
    /// use the_q::{Q, Rat};
    ///
    /// assert_eq!(Q::checked_mul(Q::zero(), Q::PosSat), Some(Rat::zero()));
    /// assert_eq!(Q::checked_mul(Q::one(), Q::PosSat), None);
    /// ```
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

    /// Ghost mirror of [`Q::number_times_inf`]. See [`Q::spec_add_numbers`].
    pub open spec fn spec_number_times_inf(x: Rat, inf_pos: bool) -> Q {
        if x.n() == 0 {
            Q::Nan
        } else if (x.n() > 0) == inf_pos {
            Q::PosInf
        } else {
            Q::NegInf
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
            r == Q::spec_number_times_inf(x, inf_pos),
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
    /// Ghost mirror of [`Q::neg`]'s match. See [`Q::spec_add`]. The `Number`
    /// arm reconstructs the negated pair through `from_raw_spec` rather than
    /// calling the exec-only [`Rat::neg`], which cannot appear in a spec
    /// position.
    pub open spec fn spec_neg(a: Q) -> Q {
        match a {
            Q::Number(x) => Q::Number(Rat::from_raw_spec((0 - x.n()) as i64, x.d() as i64)),
            Q::PosSat => Q::NegSat,
            Q::NegSat => Q::PosSat,
            Q::PosInf => Q::NegInf,
            Q::NegInf => Q::PosInf,
            Q::Nan => Q::Nan,
        }
    }

    /// `spec_neg` preserves `wf`, proven independently of the exec `neg`
    /// (which a `proof fn` cannot call): the `Number` arm's reconstructed
    /// pair carries the same `gcd` and budget as `x`'s, negation changing
    /// neither.
    pub proof fn lemma_spec_neg_wf(a: Q)
        requires
            a.wf(),
        ensures
            Q::spec_neg(a).wf(),
    {
        match a {
            Q::Number(x) => {
                let nx = Rat::from_raw_spec((0 - x.n()) as i64, x.d() as i64);
                Rat::lemma_from_raw_spec_components((0 - x.n()) as i64, x.d() as i64);
                assert(((0 - x.n()) as i64) as int == 0 - x.n());
                assert((x.d() as i64) as int == x.d());
                assert(crate::model::gcd_int(nx.n(), nx.d()) == crate::model::gcd_int(x.n(), x.d()));
            },
            _ => {},
        }
    }

    /// `-self`, exact and total; saturations and infinities negate onto each other.
    ///
    /// ```
    /// use the_q::Q;
    ///
    /// assert_eq!(Q::one().neg(), Q::neg_one());
    /// assert_eq!(Q::PosSat.neg(), Q::NegSat);
    /// assert_eq!(Q::PosInf.neg(), Q::NegInf);
    /// assert!(Q::Nan.neg().is_nan());
    /// ```
    pub fn neg(self) -> (r: Q)
        requires
            self.wf(),
        ensures
            r.wf(),
            r == Q::spec_neg(self),
            // Negation permutes the classes rather than collapsing any of them.
            r.spec_is_number() == self.spec_is_number(),
            r.spec_is_saturated() == self.spec_is_saturated(),
            r.spec_is_infinite() == self.spec_is_infinite(),
            r.spec_is_nan() == self.spec_is_nan(),
            r.spec_is_zero() == self.spec_is_zero(),
    {
        match self {
            Q::Number(x) => {
                let nx = x.neg();
                proof {
                    assert(((0 - x.n()) as i64) as int == 0 - x.n());
                    assert((x.d() as i64) as int == x.d());
                    Rat::lemma_from_raw_spec_components((0 - x.n()) as i64, x.d() as i64);
                    Rat::lemma_extensional(nx, Rat::from_raw_spec((0 - x.n()) as i64, x.d() as i64));
                }
                Q::Number(nx)
            },
            Q::PosSat => Q::NegSat,
            Q::NegSat => Q::PosSat,
            Q::PosInf => Q::NegInf,
            Q::NegInf => Q::PosInf,
            Q::Nan => Q::Nan,
        }
    }

    /// `|self|`, exact and total. Not injective on the specials, which is why
    /// `neg` carries class-preservation postconditions and this does not.
    ///
    /// ```
    /// use the_q::Q;
    ///
    /// assert_eq!(Q::neg_one().abs(), Q::one());
    /// assert_eq!(Q::NegSat.abs(), Q::PosSat);
    /// assert_eq!(Q::NegInf.abs(), Q::PosInf);
    /// ```
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
// IEEE 754-2019 withdrew the NaN-ignoring `minNum`/`maxNum`; these follow the
// NaN-propagating `minimum`/`maximum`.

impl Q {
    /// The smaller of `a` and `b`, propagating `Nan`; not `Ord`-based selection.
    ///
    /// ```
    /// use the_q::Q;
    ///
    /// assert_eq!(Q::min(Q::zero(), Q::one()), Q::zero());
    /// // Unlike `Ord::min`, a `Nan` operand makes the result `Nan`.
    /// assert!(Q::min(Q::Nan, Q::one()).is_nan());
    /// ```
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
    ///
    /// ```
    /// use the_q::Q;
    ///
    /// assert_eq!(Q::max(Q::zero(), Q::one()), Q::one());
    /// assert!(Q::max(Q::Nan, Q::one()).is_nan());
    /// ```
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

    /// `a` clamped into `[lo, hi]`; `Nan` in any argument, or an inverted range,
    /// gives `Nan` rather than an endpoint that asserts a false value.
    ///
    /// ```
    /// use the_q::{Q, Rat};
    ///
    /// let half = Q::number(Rat::new(1, 2).unwrap());
    /// assert_eq!(Q::clamp(half, Q::zero(), Q::one()), half);
    /// let two = Q::number(Rat::new(2, 1).unwrap());
    /// assert_eq!(Q::clamp(two, Q::zero(), Q::one()), Q::one());
    /// // An inverted range has no consistent answer.
    /// assert!(Q::clamp(half, Q::one(), Q::zero()).is_nan());
    /// ```
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
    /// Ghost mirror of [`Q::div_numbers`]. See [`Q::spec_add_numbers`].
    pub open spec fn spec_div_numbers(x: Rat, y: Rat) -> Q {
        let n = crate::q::div_n(x, y);
        let d = crate::q::div_d(x, y);
        if crate::model::magnitude_fits(n, d) {
            Q::Number(crate::round::round_frac(n, d, Dir::Nearest))
        } else if n > 0 {
            Q::PosSat
        } else {
            Q::NegSat
        }
    }

    /// `x / y` for representable `x`, `y != 0`; saturates rather than clamps.
    fn div_numbers(x: Rat, y: Rat) -> (r: Q)
        requires
            x.wf(),
            y.wf(),
            y.n() != 0,
        ensures
            r.wf(),
            !r.spec_is_nan(),
            !r.spec_is_infinite(),
            r == Q::spec_div_numbers(x, y),
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

    /// Ghost mirror of [`Q::sat_div_number`]. See [`Q::spec_add_numbers`].
    pub open spec fn spec_sat_div_number(pos: bool, y: Rat) -> Q {
        if y.n() == 0 {
            if pos {
                Q::PosInf
            } else {
                Q::NegInf
            }
        } else if y.n() > 0 {
            if y.n() <= y.d() {
                if pos {
                    Q::PosSat
                } else {
                    Q::NegSat
                }
            } else {
                Q::Nan
            }
        } else {
            if y.n() >= 0 - y.d() {
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

    /// `Sat / y`. Sound while `|y| <= 1` (inclusive); above that the image
    /// contains representable values and the result is `Nan`.
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
            r == Q::spec_sat_div_number(pos, y),
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

    /// Ghost mirror of [`Q::div`]'s match. See [`Q::spec_add`].
    pub open spec fn spec_div(a: Q, b: Q) -> Q {
        match (a, b) {
            (Q::Nan, _) => Q::Nan,
            (_, Q::Nan) => Q::Nan,
            (Q::Number(x), Q::Number(y)) => {
                if y.n() == 0 {
                    if x.n() == 0 {
                        Q::Nan
                    } else if x.n() > 0 {
                        Q::PosInf
                    } else {
                        Q::NegInf
                    }
                } else {
                    Q::spec_div_numbers(x, y)
                }
            },
            (Q::Number(x), Q::PosSat) => if x.n() == 0 {
                Q::Number(Rat::from_raw_spec(0, 1))
            } else {
                Q::Nan
            },
            (Q::Number(x), Q::NegSat) => if x.n() == 0 {
                Q::Number(Rat::from_raw_spec(0, 1))
            } else {
                Q::Nan
            },
            (Q::Number(_), Q::PosInf) => Q::Number(Rat::from_raw_spec(0, 1)),
            (Q::Number(_), Q::NegInf) => Q::Number(Rat::from_raw_spec(0, 1)),
            (Q::PosSat, Q::Number(y)) => Q::spec_sat_div_number(true, y),
            (Q::NegSat, Q::Number(y)) => Q::spec_sat_div_number(false, y),
            (Q::PosSat, Q::PosSat) => Q::Nan,
            (Q::PosSat, Q::NegSat) => Q::Nan,
            (Q::NegSat, Q::PosSat) => Q::Nan,
            (Q::NegSat, Q::NegSat) => Q::Nan,
            (Q::PosSat, Q::PosInf) => Q::Number(Rat::from_raw_spec(0, 1)),
            (Q::PosSat, Q::NegInf) => Q::Number(Rat::from_raw_spec(0, 1)),
            (Q::NegSat, Q::PosInf) => Q::Number(Rat::from_raw_spec(0, 1)),
            (Q::NegSat, Q::NegInf) => Q::Number(Rat::from_raw_spec(0, 1)),
            (Q::PosInf, Q::Number(y)) => if y.n() < 0 {
                Q::NegInf
            } else {
                Q::PosInf
            },
            (Q::NegInf, Q::Number(y)) => if y.n() < 0 {
                Q::PosInf
            } else {
                Q::NegInf
            },
            (Q::PosInf, Q::PosSat) => Q::PosInf,
            (Q::PosInf, Q::NegSat) => Q::NegInf,
            (Q::NegInf, Q::PosSat) => Q::NegInf,
            (Q::NegInf, Q::NegSat) => Q::PosInf,
            (Q::PosInf, Q::PosInf) => Q::Nan,
            (Q::PosInf, Q::NegInf) => Q::Nan,
            (Q::NegInf, Q::PosInf) => Q::Nan,
            (Q::NegInf, Q::NegInf) => Q::Nan,
        }
    }

    /// `a / b`, total. Division by zero follows IEEE 754 uniformly, so that
    /// `recip(x) == div(one, x)` holds at zero. `Sat / Inf` is exactly `0` and
    /// `Inf / Sat` a signed infinity, because saturation denotes finite reals.
    ///
    /// ```
    /// use the_q::{Q, Rat};
    ///
    /// assert_eq!(Q::div(Q::one(), Q::one()), Q::one());
    /// // Division by zero follows IEEE 754: a signed infinity, and `0/0` is `Nan`.
    /// assert_eq!(Q::div(Q::one(), Q::zero()), Q::PosInf);
    /// assert!(Q::div(Q::zero(), Q::zero()).is_nan());
    /// ```
    pub fn div(a: Q, b: Q) -> (r: Q)
        requires
            a.wf(),
            b.wf(),
        ensures
            r.wf(),
            r == Q::spec_div(a, b),
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

    /// `1 / self`, total, defined as `div(one, self)` (`theorem_recip_is_div_one`).
    /// Exact on a nonzero `Number`: swapping a canonical pair cannot round.
    ///
    /// ```
    /// use the_q::{Q, Rat};
    ///
    /// let two = Q::number(Rat::new(2, 1).unwrap());
    /// assert_eq!(two.recip(), Q::number(Rat::new(1, 2).unwrap()));
    /// assert_eq!(Q::zero().recip(), Q::PosInf);
    /// ```
    pub fn recip(self) -> (r: Q)
        requires
            self.wf(),
        ensures
            r.wf(),
            self.spec_is_nan() ==> r.spec_is_nan(),
            // theorem_q_recip_is_div_one: true by definition, not derived —
            // recip's only body is this call.
            r == Q::spec_div(Q::Number(Rat::from_raw_spec(1, 1)), self),
    {
        // The cell-by-cell table is deliberately not restated in ghost form: a spec
        // shaped like the table verifies with a shared mistake.
        Q::div(Q::one(), self)
    }

    /// `a / b` as a `Rat`, `None` otherwise, including a zero divisor.
    ///
    /// ```
    /// use the_q::{Q, Rat};
    ///
    /// assert_eq!(Q::checked_div(Q::one(), Q::one()), Some(Rat::one()));
    /// assert_eq!(Q::checked_div(Q::one(), Q::zero()), None);
    /// ```
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
// `NegSat < Number < PosSat` strictly, by I2; the position of `Nan` is a free
// choice.

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
    ///
    /// ```
    /// use the_q::Q;
    ///
    /// assert_eq!(Q::compare(Q::zero(), Q::one()), -1);
    /// assert_eq!(Q::compare(Q::one(), Q::one()), 0);
    /// // `Nan` sorts last, above every other state.
    /// assert_eq!(Q::compare(Q::PosInf, Q::Nan), -1);
    /// ```
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
    ///
    /// ```
    /// use the_q::Q;
    ///
    /// assert!(Q::lt(Q::zero(), Q::one()));
    /// assert!(!Q::lt(Q::one(), Q::one()));
    /// ```
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
    ///
    /// ```
    /// use the_q::Q;
    ///
    /// assert!(Q::le(Q::one(), Q::one()));
    /// assert!(!Q::le(Q::one(), Q::zero()));
    /// ```
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
    ///
    /// ```
    /// use the_q::Q;
    ///
    /// assert!(Q::gt(Q::one(), Q::zero()));
    /// assert!(!Q::gt(Q::zero(), Q::zero()));
    /// ```
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
    ///
    /// ```
    /// use the_q::Q;
    ///
    /// assert!(Q::ge(Q::one(), Q::one()));
    /// assert!(!Q::ge(Q::zero(), Q::one()));
    /// ```
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

/// The order is total: every pair is comparable, `Nan` included.
pub proof fn theorem_order_total(a: Q, b: Q)
    requires
        a.wf(),
        b.wf(),
    ensures
        Q::spec_le(a, b) || Q::spec_le(b, a),
{
}

/// Antisymmetry against *structural* equality: `a <= b <= a` gives `a == b`,
/// not merely `spec_eq`. This is what makes the derived `Eq`/`Hash` sound
/// beside the hand-written `Ord`; the `Number` case is kernel canonicality.
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

/// `NegInf` is strictly below and `Nan` strictly above every other value, so
/// folds can start there and the extremes are unique.
pub proof fn theorem_order_extremes(q: Q)
    ensures
        Q::spec_le(Q::NegInf, q),
        Q::spec_le(q, Q::Nan),
        q != Q::NegInf ==> !Q::spec_le(q, Q::NegInf),
        q != Q::Nan ==> !Q::spec_le(Q::Nan, q),
{
}

/// Trichotomy: exactly one of `a < b`, `a == b`, `b < a` holds.
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

/// `min`'s contract admits exactly one answer; on a tie, canonicality makes the
/// two representations one.
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

/// `clamp`'s contract admits exactly one answer. Without its last three clauses
/// a `clamp` that always returned `lo` would verify.
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

/// `(min(a, b), max(a, b))` is `(a, b)` or `(b, a)`: a two-element sort.
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

/// `min` is the greatest lower bound: `q <= min(a, b)` iff `q <= a` and `q <= b`.
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

/// The component-wise `spec_in_unit_interval` agrees with the order-based
/// `0 <= q <= 1` on a `Number`; no special is in `[0, 1]`.
pub proof fn theorem_unit_interval_agrees_with_order(q: Q)
    requires
        q.wf(),
    ensures
        q.spec_in_unit_interval() <==> (q.spec_is_number() && Q::spec_le(
            Q::Number(Rat::from_raw_spec(0, 1)),
            q,
        ) && Q::spec_le(q, Q::Number(Rat::from_raw_spec(1, 1)))),
{
    Rat::lemma_from_raw_spec_components(0, 1);
    Rat::lemma_from_raw_spec_components(1, 1);
}

/// `spec_is_zero` holds only of `Number(0/1)` and `spec_is_one` only of
/// `Number(1/1)`: the enum-level form of canonicality.
pub proof fn theorem_zero_one_unique_repr(q: Q)
    requires
        q.wf(),
    ensures
        q.spec_is_zero() <==> q == Q::Number(Rat::from_raw_spec(0, 1)),
        q.spec_is_one() <==> q == Q::Number(Rat::from_raw_spec(1, 1)),
{
    Rat::lemma_from_raw_spec_components(0, 1);
    Rat::lemma_from_raw_spec_components(1, 1);
    match q {
        Q::Number(x) => {
            if x.n() == 0 {
                assert(x.d() == 1);
                Rat::lemma_extensional(x, Rat::from_raw_spec(0, 1));
            }
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
                assert(x.d() == 1);
                Rat::lemma_extensional(x, Rat::from_raw_spec(1, 1));
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
    /// Delegates to the verified [`Q::compare`]. Do not use for selection:
    /// `Ord`-based `min(Nan, Number(5))` asserts the value 5.
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
