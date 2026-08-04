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

use crate::types::Rat;

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

    /// The exact rational `num / den`, canonicalised, or a special.
    ///
    /// Unlike [`Rat::new`] this is **total**: `den == 0` is no longer a failure
    /// to be reported out-of-band but a value in the type, resolved by the
    /// IEEE 754 convention of issue #26 §4 — `x/0` takes the positive-side limit
    /// by fiat, exactly as IEEE does for `+0`, and `0/0` carries no information.
    ///
    /// A pair that is finite but does not fit the budget saturates by sign
    /// rather than failing. `Rat::new` remains available for callers that want
    /// the partial, allocation-free answer.
    pub fn new(num: i64, den: i64) -> (r: Q)
        ensures
            r.wf(),
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
            match Rat::new(num, den) {
                Some(x) => Q::Number(x),
                // `Rat::new` fails only on `den == 0` (handled above) or on a
                // reduced pair outside the budget, which is a genuine magnitude
                // overflow. The sign of `num/den` is the sign of the product of
                // the signs, and neither is zero here: `num == 0` would reduce
                // to `0/1`, which always fits.
                None => if (num > 0) == (den > 0) {
                    Q::PosSat
                } else {
                    Q::NegSat
                },
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

/// The order is antisymmetric, and on representations `spec_eq` really is
/// identity — which is what keeps derived `PartialEq`/`Hash` consistent with it.
pub proof fn theorem_order_antisymmetric(a: Q, b: Q)
    requires
        a.wf(),
        b.wf(),
        Q::spec_le(a, b),
        Q::spec_le(b, a),
    ensures
        Q::spec_eq(a, b),
{
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
