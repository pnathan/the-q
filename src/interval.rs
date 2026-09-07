//! [`QI`], a closed rational interval on the directed rounding modes.
//!
//! Lower endpoints round `Down`, upper endpoints `Up`, so enclosure is a
//! corollary of R2 and the monotonicity of the exact operations; no new
//! rounding proof is needed. Endpoints are crate-private and ordered:
//! `new` guards `lo <= hi` at run time, `checked_new` is total.

use verus_builtin_macros::verus;

#[allow(unused_imports)]
use verus_builtin::*;
#[allow(unused_imports)]
use vstd::prelude::*;

use crate::ext::Q;
#[allow(unused_imports)]
use crate::model::*;
#[allow(unused_imports)]
use crate::q::*;
#[allow(unused_imports)]
use crate::types::MAX_MAG;
use crate::types::{Dir, Rat};

verus! {

/// A closed rational interval `[lo, hi]`. Endpoints are private; use
/// [`QI::checked_new`] for untrusted endpoints.
///
/// ```compile_fail
/// use the_q::{QI, Rat};
/// let _ = QI { lo: Rat::zero(), hi: Rat::one() };
/// ```
///
/// ```compile_fail
/// use the_q::{QI, Rat};
/// let mut i = QI::exact(Rat::zero());
/// i.lo = Rat::one();
/// ```
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct QI {
    /// The lower endpoint. Always computed with [`Dir::Down`].
    pub(crate) lo: Rat,
    /// The upper endpoint. Always computed with [`Dir::Up`].
    pub(crate) hi: Rat,
}

impl QI {
    /// The lower endpoint in specifications.
    pub closed spec fn spec_lower(self) -> Rat {
        self.lo
    }

    /// The upper endpoint in specifications.
    pub closed spec fn spec_upper(self) -> Rat {
        self.hi
    }

    /// The lower endpoint.
    ///
    /// ```
    /// use the_q::{QI, Rat};
    ///
    /// let i = QI::new(Rat::new(1, 2).unwrap(), Rat::new(3, 2).unwrap());
    /// assert_eq!(i.lower(), Rat::new(1, 2).unwrap());
    /// ```
    pub fn lower(&self) -> (r: Rat)
        ensures r == self.spec_lower(),
    {
        proof { reveal(QI::spec_lower); }
        self.lo
    }

    /// The upper endpoint.
    ///
    /// ```
    /// use the_q::{QI, Rat};
    ///
    /// let i = QI::new(Rat::new(1, 2).unwrap(), Rat::new(3, 2).unwrap());
    /// assert_eq!(i.upper(), Rat::new(3, 2).unwrap());
    /// ```
    pub fn upper(&self) -> (r: Rat)
        ensures r == self.spec_upper(),
    {
        proof { reveal(QI::spec_upper); }
        self.hi
    }

    /// The interval invariant: both endpoints well-formed and correctly
    /// ordered.
    pub open spec fn wf(self) -> bool {
        &&& self.spec_lower().wf()
        &&& self.spec_upper().wf()
        &&& q_le(self.spec_lower(), self.spec_upper())
    }

    /// The degenerate interval `[a, a]`.
    ///
    /// ```
    /// use the_q::{QI, Rat};
    ///
    /// let i = QI::exact(Rat::new(1, 2).unwrap());
    /// assert_eq!(i.lower(), Rat::new(1, 2).unwrap());
    /// assert_eq!(i.upper(), Rat::new(1, 2).unwrap());
    /// ```
    pub fn exact(a: Rat) -> (r: QI)
        requires
            a.wf(),
        ensures
            r.wf(),
            r.spec_lower() == a,
            r.spec_upper() == a,
    {
        QI { lo: a, hi: a }
    }

    /// `[lo, hi]`, requiring the endpoints to be ordered.
    ///
    /// ```
    /// use the_q::{QI, Rat};
    ///
    /// let i = QI::new(Rat::zero(), Rat::one());
    /// assert_eq!(i.lower(), Rat::zero());
    /// assert_eq!(i.upper(), Rat::one());
    /// ```
    ///
    /// Panics when `lo > hi`. Use [`QI::checked_new`] for untrusted input:
    ///
    /// ```should_panic
    /// use the_q::{QI, Rat};
    ///
    /// let _ = QI::new(Rat::one(), Rat::zero());
    /// ```
    pub fn new(lo: Rat, hi: Rat) -> (r: QI)
        requires
            lo.wf(),
            hi.wf(),
            q_le(lo, hi),
        ensures
            r.wf(),
            r.spec_lower() == lo,
            r.spec_upper() == hi,
    {
        crate::q::require_condition(
            Rat::le(lo, hi),
            "the-q: QI::new requires lo <= hi. Use QI::checked_new for untrusted input.",
        );
        QI { lo, hi }
    }

    /// Constructs `[lo, hi]`, returning `None` when the endpoints are reversed.
    ///
    /// ```
    /// use the_q::{QI, Rat};
    ///
    /// assert!(QI::checked_new(Rat::zero(), Rat::one()).is_some());
    /// assert!(QI::checked_new(Rat::one(), Rat::zero()).is_none());
    /// ```
    pub fn checked_new(lo: Rat, hi: Rat) -> (r: Option<QI>)
        requires
            lo.wf(),
            hi.wf(),
        ensures
            r.is_some() <==> q_le(lo, hi),
            r.is_some() ==> r.unwrap().wf(),
            r.is_some() ==> r.unwrap().spec_lower() == lo,
            r.is_some() ==> r.unwrap().spec_upper() == hi,
    {
        if Rat::le(lo, hi) {
            Some(QI { lo, hi })
        } else {
            None
        }
    }

    /// Whether `x` lies inside the interval.
    ///
    /// ```
    /// use the_q::{QI, Rat};
    ///
    /// let i = QI::new(Rat::zero(), Rat::one());
    /// assert!(i.contains(Rat::new(1, 2).unwrap()));
    /// assert!(!i.contains(Rat::new(3, 2).unwrap()));
    /// ```
    pub fn contains(&self, x: Rat) -> (r: bool)
        requires
            self.wf(),
            x.wf(),
        ensures
            r <==> (q_le(self.spec_lower(), x) && q_le(x, self.spec_upper())),
    {
        Rat::le(self.lo, x) && Rat::le(x, self.hi)
    }

    /// An upward-rounded `hi - lo`, or `None` when its magnitude exceeds the
    /// representable range.
    ///
    /// ```
    /// use the_q::{QI, Rat};
    ///
    /// let i = QI::new(Rat::zero(), Rat::one());
    /// assert_eq!(i.checked_width(), Some(Rat::one()));
    /// ```
    pub fn checked_width(&self) -> (r: Option<Rat>)
        requires
            self.wf(),
        ensures
            r.is_none() <==> crate::round::saturated(
                sub_n(self.spec_upper(), self.spec_lower()),
                prod_d(self.spec_upper(), self.spec_lower()),
            ),
            r.is_some() ==> r.unwrap().wf(),
            r.is_some() ==> q_ge_frac(
                r.unwrap(),
                sub_n(self.spec_upper(), self.spec_lower()),
                prod_d(self.spec_upper(), self.spec_lower()),
            ),
            r.is_some() ==> r.unwrap().n() >= 0,
    {
        proof {
            reveal(QI::spec_lower);
            reveal(QI::spec_upper);
            theorem_qi_exact_width_nonnegative(*self);
        }
        let result = Rat::checked_sub_dir(self.hi, self.lo, Dir::Up);
        proof {
            reveal(QI::spec_lower);
            reveal(QI::spec_upper);
            theorem_qi_exact_width_nonnegative(*self);
            assert(prod_d(self.hi, self.lo) > 0);
            assert(sub_n(self.hi, self.lo) >= 0);
            if result.is_some() {
                assert(result.unwrap().n() * prod_d(self.hi, self.lo)
                    >= sub_n(self.hi, self.lo) * result.unwrap().d());
                assert(sub_n(self.hi, self.lo) * result.unwrap().d() >= 0) by (nonlinear_arith)
                    requires
                        sub_n(self.hi, self.lo) >= 0,
                        result.unwrap().d() > 0,
                ;
                assert(result.unwrap().n() * prod_d(self.hi, self.lo) >= 0);
                if result.unwrap().n() < 0 {
                    vstd::arithmetic::mul::lemma_mul_strictly_positive(
                        -result.unwrap().n(),
                        prod_d(self.hi, self.lo),
                    );
                    assert(
                        result.unwrap().n() * prod_d(self.hi, self.lo)
                            == -((-result.unwrap().n()) * prod_d(self.hi, self.lo))
                    ) by (nonlinear_arith);
                    assert(false);
                }
            }
        }
        result
    }

    /// The upward-rounded width, with magnitude overflow reported as
    /// [`Q::PosSat`]. Zero means the computation stayed on the exact path.
    ///
    /// ```
    /// use the_q::{QI, Rat, Q};
    ///
    /// let i = QI::new(Rat::zero(), Rat::one());
    /// assert_eq!(i.width(), Q::Number(Rat::one()));
    /// ```
    pub fn width(&self) -> (r: Q)
        requires
            self.wf(),
        ensures
            r.wf(),
            !crate::round::saturated(
                sub_n(self.spec_upper(), self.spec_lower()),
                prod_d(self.spec_upper(), self.spec_lower()),
            ) ==> r.spec_is_number(),
            crate::round::saturated(
                sub_n(self.spec_upper(), self.spec_lower()),
                prod_d(self.spec_upper(), self.spec_lower()),
            ) ==> r == Q::PosSat,
            r != Q::NegSat,
            !r.spec_is_infinite(),
            !r.spec_is_nan(),
    {
        match self.checked_width() {
            Some(width) => Q::Number(width),
            None => Q::PosSat,
        }
    }

    /// `[a.lo + b.lo, a.hi + b.hi]`, outward rounded; `wf` by
    /// `lemma_directed_round_order`.
    ///
    /// Enclosure: if `a` contains `x` and `b` contains `y`, `QI::add(a, b)`
    /// contains `x + y`.
    ///
    /// ```
    /// use the_q::{QI, Rat};
    ///
    /// let a = QI::new(Rat::zero(), Rat::one());
    /// let b = QI::new(Rat::new(1, 2).unwrap(), Rat::new(3, 2).unwrap());
    /// let sum = QI::add(a, b);
    /// let (x, y) = (Rat::new(1, 4).unwrap(), Rat::one());
    /// assert!(a.contains(x) && b.contains(y));
    /// assert!(sum.contains(Rat::add(x, y)));
    /// ```
    pub fn add(a: QI, b: QI) -> (r: QI)
        requires
            a.wf(),
            b.wf(),
        ensures
            r.wf(),
            !crate::round::saturated(add_n(a.spec_lower(), b.spec_lower()), prod_d(a.spec_lower(), b.spec_lower())) ==> q_le_frac(
                r.spec_lower(),
                add_n(a.spec_lower(), b.spec_lower()),
                prod_d(a.spec_lower(), b.spec_lower()),
            ),
            !crate::round::saturated(add_n(a.spec_upper(), b.spec_upper()), prod_d(a.spec_upper(), b.spec_upper())) ==> q_ge_frac(
                r.spec_upper(),
                add_n(a.spec_upper(), b.spec_upper()),
                prod_d(a.spec_upper(), b.spec_upper()),
            ),
    {
        let lo = Rat::add_dir(a.lo, b.lo, Dir::Down);
        let hi = Rat::add_dir(a.hi, b.hi, Dir::Up);
        proof {
            crate::q::lemma_op_widths(a.lo, b.lo);
            crate::q::lemma_op_widths(a.hi, b.hi);
            if !crate::round::saturated(add_n(a.lo, b.lo), prod_d(a.lo, b.lo)) {
                crate::round::lemma_r2_directed(add_n(a.lo, b.lo), prod_d(a.lo, b.lo));
            }
            if !crate::round::saturated(add_n(a.hi, b.hi), prod_d(a.hi, b.hi)) {
                crate::round::lemma_r2_directed(add_n(a.hi, b.hi), prod_d(a.hi, b.hi));
            }
            // The exact lo-sum never exceeds the exact hi-sum. This is a direct
            // instance of the endpoint-order lemma with x := a.hi, y := b.hi.
            lemma_add_endpoint_order(
                a.lo.n(),
                a.lo.d(),
                b.lo.n(),
                b.lo.d(),
                a.hi.n(),
                a.hi.d(),
                b.hi.n(),
                b.hi.d(),
            );
            lemma_directed_round_order(
                add_n(a.lo, b.lo),
                prod_d(a.lo, b.lo),
                add_n(a.hi, b.hi),
                prod_d(a.hi, b.hi),
            );
        }
        QI { lo, hi }
    }

    /// `[a.lo - b.hi, a.hi - b.lo]`, outward rounded.
    ///
    /// ```
    /// use the_q::{QI, Rat};
    ///
    /// let a = QI::new(Rat::zero(), Rat::one());
    /// let b = QI::new(Rat::new(1, 2).unwrap(), Rat::new(3, 2).unwrap());
    /// let diff = QI::sub(a, b);
    /// let (x, y) = (Rat::new(1, 4).unwrap(), Rat::one());
    /// assert!(a.contains(x) && b.contains(y));
    /// assert!(diff.contains(Rat::sub(x, y)));
    /// ```
    pub fn sub(a: QI, b: QI) -> (r: QI)
        requires
            a.wf(),
            b.wf(),
        ensures
            r.wf(),
            !crate::round::saturated(sub_n(a.spec_lower(), b.spec_upper()), prod_d(a.spec_lower(), b.spec_upper())) ==> q_le_frac(
                r.spec_lower(),
                sub_n(a.spec_lower(), b.spec_upper()),
                prod_d(a.spec_lower(), b.spec_upper()),
            ),
            !crate::round::saturated(sub_n(a.spec_upper(), b.spec_lower()), prod_d(a.spec_upper(), b.spec_lower())) ==> q_ge_frac(
                r.spec_upper(),
                sub_n(a.spec_upper(), b.spec_lower()),
                prod_d(a.spec_upper(), b.spec_lower()),
            ),
    {
        let lo = Rat::sub_dir(a.lo, b.hi, Dir::Down);
        let hi = Rat::sub_dir(a.hi, b.lo, Dir::Up);
        proof {
            crate::q::lemma_op_widths(a.lo, b.hi);
            crate::q::lemma_op_widths(a.hi, b.lo);
            if !crate::round::saturated(sub_n(a.lo, b.hi), prod_d(a.lo, b.hi)) {
                crate::round::lemma_r2_directed(sub_n(a.lo, b.hi), prod_d(a.lo, b.hi));
            }
            if !crate::round::saturated(sub_n(a.hi, b.lo), prod_d(a.hi, b.lo)) {
                crate::round::lemma_r2_directed(sub_n(a.hi, b.lo), prod_d(a.hi, b.lo));
            }
            // The exact lo-difference never exceeds the exact hi-difference.
            // Apply the endpoint-order lemma to (a.lo, -b.hi) against
            // (a.hi, -b.lo). `b.wf()` gives `b.lo <= b.hi`. Negating both sides
            // flips that order.
            assert((-b.hi.n()) * b.lo.d() <= (-b.lo.n()) * b.hi.d()) by (nonlinear_arith)
                requires
                    b.lo.n() * b.hi.d() <= b.hi.n() * b.lo.d(),
            ;
            lemma_add_endpoint_order(
                a.lo.n(),
                a.lo.d(),
                -b.hi.n(),
                b.hi.d(),
                a.hi.n(),
                a.hi.d(),
                -b.lo.n(),
                b.lo.d(),
            );
            // Restate the lemma's output (in raw `an·bd + bn·ad` form) as the
            // `sub_n`/`prod_d` comparison `lemma_directed_round_order` needs.
            assert(
                sub_n(a.lo, b.hi) * prod_d(a.hi, b.lo) <= sub_n(a.hi, b.lo) * prod_d(a.lo, b.hi)
            ) by (nonlinear_arith)
                requires
                    (a.lo.n() * b.hi.d() + (-b.hi.n()) * a.lo.d()) * (a.hi.d() * b.lo.d())
                        <= (a.hi.n() * b.lo.d() + (-b.lo.n()) * a.hi.d()) * (a.lo.d() * b.hi.d()),
            ;
            lemma_directed_round_order(
                sub_n(a.lo, b.hi),
                prod_d(a.lo, b.hi),
                sub_n(a.hi, b.lo),
                prod_d(a.hi, b.lo),
            );
        }
        QI { lo, hi }
    }

    /// Interval negation: `[-hi, -lo]`. Exact.
    ///
    /// ```
    /// use the_q::{QI, Rat};
    ///
    /// let i = QI::new(Rat::zero(), Rat::one());
    /// let n = QI::neg(i);
    /// assert_eq!(n.lower(), Rat::new(-1, 1).unwrap());
    /// assert_eq!(n.upper(), Rat::zero());
    /// ```
    pub fn neg(a: QI) -> (r: QI)
        requires
            a.wf(),
        ensures
            r.wf(),
            r.spec_lower().n() == -a.spec_upper().n(),
            r.spec_upper().n() == -a.spec_lower().n(),
    {
        let lo = a.hi.neg();
        let hi = a.lo.neg();
        proof {
            assert(q_le(lo, hi)) by (nonlinear_arith)
                requires
                    a.lo.n() * a.hi.d() <= a.hi.n() * a.lo.d(),
                    lo.n() == -a.hi.n(),
                    lo.d() == a.hi.d(),
                    hi.n() == -a.lo.n(),
                    hi.d() == a.lo.d(),
            ;
        }
        QI { lo, hi }
    }

    /// Min and max of the four outward-rounded corner products;
    /// `theorem_interval_mul_contains` is the corner rule.
    ///
    /// ```
    /// use the_q::{QI, Rat};
    ///
    /// let a = QI::new(Rat::zero(), Rat::new(2, 1).unwrap());
    /// let b = QI::new(Rat::new(-1, 1).unwrap(), Rat::one());
    /// let p = QI::mul(a, b);
    /// assert_eq!(p.lower(), Rat::new(-2, 1).unwrap());
    /// assert_eq!(p.upper(), Rat::new(2, 1).unwrap());
    /// ```
    pub fn mul(a: QI, b: QI) -> (r: QI)
        requires
            a.wf(),
            b.wf(),
        ensures
            r.wf(),
    {
        let ll_lo = Rat::mul_dir(a.lo, b.lo, Dir::Down);
        let lh_lo = Rat::mul_dir(a.lo, b.hi, Dir::Down);
        let hl_lo = Rat::mul_dir(a.hi, b.lo, Dir::Down);
        let hh_lo = Rat::mul_dir(a.hi, b.hi, Dir::Down);
        let ll_hi = Rat::mul_dir(a.lo, b.lo, Dir::Up);
        let lh_hi = Rat::mul_dir(a.lo, b.hi, Dir::Up);
        let hl_hi = Rat::mul_dir(a.hi, b.lo, Dir::Up);
        let hh_hi = Rat::mul_dir(a.hi, b.hi, Dir::Up);
        let lo_m1 = Rat::min(ll_lo, lh_lo);
        let lo_m2 = Rat::min(hl_lo, hh_lo);
        let lo = Rat::min(lo_m1, lo_m2);
        let hi_m1 = Rat::max(ll_hi, lh_hi);
        let hi_m2 = Rat::max(hl_hi, hh_hi);
        let hi = Rat::max(hi_m1, hi_m2);
        proof {
            crate::q::lemma_op_widths(a.lo, b.lo);
            lemma_le_trans(lo, lo_m1, ll_lo);
            lemma_directed_round_order(
                mul_n(a.lo, b.lo),
                prod_d(a.lo, b.lo),
                mul_n(a.lo, b.lo),
                prod_d(a.lo, b.lo),
            );
            lemma_le_trans(ll_hi, hi_m1, hi);
            lemma_le_trans(ll_lo, ll_hi, hi);
            lemma_le_trans(lo, ll_lo, hi);
        }
        QI { lo, hi }
    }

    /// The union hull of two intervals: the smallest interval containing
    /// both.
    ///
    /// ```
    /// use the_q::{QI, Rat};
    ///
    /// let a = QI::new(Rat::zero(), Rat::one());
    /// let b = QI::new(Rat::new(2, 1).unwrap(), Rat::new(3, 1).unwrap());
    /// let h = QI::hull(a, b);
    /// assert_eq!(h.lower(), Rat::zero());
    /// assert_eq!(h.upper(), Rat::new(3, 1).unwrap());
    /// ```
    pub fn hull(a: QI, b: QI) -> (r: QI)
        requires
            a.wf(),
            b.wf(),
        ensures
            r.wf(),
            r.spec_lower() == a.spec_lower() || r.spec_lower() == b.spec_lower(),
            r.spec_upper() == a.spec_upper() || r.spec_upper() == b.spec_upper(),
            q_le(r.spec_lower(), a.spec_lower()),
            q_le(r.spec_lower(), b.spec_lower()),
            q_le(a.spec_upper(), r.spec_upper()),
            q_le(b.spec_upper(), r.spec_upper()),
    {
        let lo = Rat::min(a.lo, b.lo);
        let hi = Rat::max(a.hi, b.hi);
        proof {
            crate::q::lemma_le_trans(lo, a.lo, a.hi);
            crate::q::lemma_le_trans(lo, a.hi, hi);
        }
        QI { lo, hi }
    }
}

/// The mathematical width of a well-formed interval is nonnegative and has a
/// positive denominator, independently of whether it fits in [`Rat`].
pub proof fn theorem_qi_exact_width_nonnegative(i: QI)
    requires
        i.wf(),
    ensures
        sub_n(i.spec_upper(), i.spec_lower()) >= 0,
        prod_d(i.spec_upper(), i.spec_lower()) > 0,
{
    reveal(QI::spec_lower);
    reveal(QI::spec_upper);
    crate::q::lemma_op_widths(i.hi, i.lo);
}

/// **The containment theorem.** If the inputs bracket their true values, the
/// interval sum brackets the true sum.
///
/// This is a direct corollary of R2. It is the purpose of the directed modes.
pub proof fn theorem_interval_add_contains(a: QI, b: QI, x: Rat, y: Rat)
    requires
        a.wf(),
        b.wf(),
        x.wf(),
        y.wf(),
        q_le(a.spec_lower(), x),
        q_le(x, a.spec_upper()),
        q_le(b.spec_lower(), y),
        q_le(y, b.spec_upper()),
    ensures
        // The exact sum of x and y lies between the exact sums of the
        // endpoints. After outward rounding it therefore lies inside
        // `QI::add(a, b)`.
        add_n(a.spec_lower(), b.spec_lower()) * prod_d(x, y) <= add_n(x, y) * prod_d(a.spec_lower(), b.spec_lower()),
        add_n(x, y) * prod_d(a.spec_upper(), b.spec_upper()) <= add_n(a.spec_upper(), b.spec_upper()) * prod_d(x, y),
{
    lemma_add_endpoint_order(
        a.lo.n(),
        a.lo.d(),
        b.lo.n(),
        b.lo.d(),
        x.n(),
        x.d(),
        y.n(),
        y.d(),
    );
    lemma_add_endpoint_order(x.n(), x.d(), y.n(), y.d(), a.hi.n(), a.hi.d(), b.hi.n(), b.hi.d());
}

/// Enclosure for subtraction: `a.lo - b.hi` is `a.lo + (-b.hi)`, so this is
/// [`theorem_interval_add_contains`] on the negation.
pub proof fn theorem_interval_sub_contains(a: QI, b: QI, x: Rat, y: Rat)
    requires
        a.wf(),
        b.wf(),
        x.wf(),
        y.wf(),
        q_le(a.spec_lower(), x),
        q_le(x, a.spec_upper()),
        q_le(b.spec_lower(), y),
        q_le(y, b.spec_upper()),
    ensures
        // The exact difference of x and y lies between the exact differences
        // of the endpoints. After outward rounding it therefore lies inside
        // `QI::sub(a, b)`.
        sub_n(a.spec_lower(), b.spec_upper()) * prod_d(x, y) <= sub_n(x, y) * prod_d(a.spec_lower(), b.spec_upper()),
        sub_n(x, y) * prod_d(a.spec_upper(), b.spec_lower()) <= sub_n(a.spec_upper(), b.spec_lower()) * prod_d(x, y),
{
    // Negating `q_le(y, b.hi)` and `q_le(b.lo, y)` gives the two hypotheses
    // that each call below needs.
    assert((-b.hi.n()) * y.d() <= (-y.n()) * b.hi.d()) by (nonlinear_arith)
        requires
            y.n() * b.hi.d() <= b.hi.n() * y.d(),
    ;
    assert((-y.n()) * b.lo.d() <= (-b.lo.n()) * y.d()) by (nonlinear_arith)
        requires
            b.lo.n() * y.d() <= y.n() * b.lo.d(),
    ;
    lemma_add_endpoint_order(
        a.lo.n(),
        a.lo.d(),
        -b.hi.n(),
        b.hi.d(),
        x.n(),
        x.d(),
        -y.n(),
        y.d(),
    );
    lemma_add_endpoint_order(
        x.n(),
        x.d(),
        -y.n(),
        y.d(),
        a.hi.n(),
        a.hi.d(),
        -b.lo.n(),
        b.lo.d(),
    );
    // Restate both outputs (in raw `an·bd + bn·ad` form) as `sub_n`/`prod_d`
    // comparisons.
    assert(sub_n(a.lo, b.hi) * prod_d(x, y) <= sub_n(x, y) * prod_d(a.lo, b.hi)) by (
    nonlinear_arith)
        requires
            (a.lo.n() * b.hi.d() + (-b.hi.n()) * a.lo.d()) * (x.d() * y.d()) <= (
            x.n() * y.d() + (-y.n()) * x.d()) * (a.lo.d() * b.hi.d()),
    ;
    assert(sub_n(x, y) * prod_d(a.hi, b.lo) <= sub_n(a.hi, b.lo) * prod_d(x, y)) by (
    nonlinear_arith)
        requires
            (x.n() * y.d() + (-y.n()) * x.d()) * (a.hi.d() * b.lo.d()) <= (
            a.hi.n() * b.lo.d() + (-b.lo.n()) * a.hi.d()) * (x.d() * y.d()),
    ;
}

/// Adding two ordered pairs of fractions preserves the order.
pub proof fn lemma_add_endpoint_order(
    an: int,
    ad: int,
    bn: int,
    bd: int,
    xn: int,
    xd: int,
    yn: int,
    yd: int,
)
    requires
        ad > 0,
        bd > 0,
        xd > 0,
        yd > 0,
        an * xd <= xn * ad,
        bn * yd <= yn * bd,
    ensures
        (an * bd + bn * ad) * (xd * yd) <= (xn * yd + yn * xd) * (ad * bd),
{
    assert((an * xd) * (bd * yd) <= (xn * ad) * (bd * yd)) by (nonlinear_arith)
        requires
            an * xd <= xn * ad,
            bd > 0,
            yd > 0,
    ;
    assert((bn * yd) * (ad * xd) <= (yn * bd) * (ad * xd)) by (nonlinear_arith)
        requires
            bn * yd <= yn * bd,
            ad > 0,
            xd > 0,
    ;
    // Distribution and rearrangement stay separate. Given the combined
    // identity, the solver must discover the factorisation itself, and it
    // burns through its budget. Given distribution as its own step, each
    // remaining goal is an associativity or commutativity shuffle of a
    // four-factor product, which the solver normalises for free.
    assert((an * bd + bn * ad) * (xd * yd) == (an * bd) * (xd * yd) + (bn * ad) * (xd * yd))
        by (nonlinear_arith);
    assert((an * bd) * (xd * yd) == (an * xd) * (bd * yd)) by (nonlinear_arith);
    assert((bn * ad) * (xd * yd) == (bn * yd) * (ad * xd)) by (nonlinear_arith);
    assert((xn * yd + yn * xd) * (ad * bd) == (xn * yd) * (ad * bd) + (yn * xd) * (ad * bd))
        by (nonlinear_arith);
    assert((xn * yd) * (ad * bd) == (xn * ad) * (bd * yd)) by (nonlinear_arith);
    assert((yn * xd) * (ad * bd) == (yn * bd) * (ad * xd)) by (nonlinear_arith);
}

/// `rl <= n1/d1 <= n2/d2 <= rh` implies `rl <= rh`, with a raw fraction in the
/// middle.
pub proof fn lemma_frac_chain_le(
    rln: int,
    rld: int,
    n1: int,
    d1: int,
    n2: int,
    d2: int,
    rhn: int,
    rhd: int,
)
    requires
        rld > 0,
        d1 > 0,
        d2 > 0,
        rhd > 0,
        rln * d1 <= n1 * rld,
        n1 * d2 <= n2 * d1,
        n2 * rhd <= rhn * d2,
    ensures
        rln * rhd <= rhn * rld,
{
    assert((rln * d1) * (d2 * rhd) <= (n1 * rld) * (d2 * rhd)) by (nonlinear_arith)
        requires
            rln * d1 <= n1 * rld,
            d2 > 0,
            rhd > 0,
    ;
    assert((n1 * d2) * (rld * rhd) <= (n2 * d1) * (rld * rhd)) by (nonlinear_arith)
        requires
            n1 * d2 <= n2 * d1,
            rld > 0,
            rhd > 0,
    ;
    assert((n2 * rhd) * (d1 * rld) <= (rhn * d2) * (d1 * rld)) by (nonlinear_arith)
        requires
            n2 * rhd <= rhn * d2,
            d1 > 0,
            rld > 0,
    ;
    // Rewrite each of the three products above into the same six-factor
    // normal form. The chain then links up.
    assert((rln * d1) * (d2 * rhd) == (rln * rhd) * (d1 * d2)) by (nonlinear_arith);
    assert((n1 * rld) * (d2 * rhd) == (n1 * d2) * (rld * rhd)) by (nonlinear_arith);
    assert((n2 * d1) * (rld * rhd) == (n2 * rhd) * (d1 * rld)) by (nonlinear_arith);
    assert((rhn * d2) * (d1 * rld) == (rhn * rld) * (d1 * d2)) by (nonlinear_arith);
    assert((rln * rhd) * (d1 * d2) <= (rhn * rld) * (d1 * d2));
    // Cancel the common positive factor `d1 * d2`.
    assert(rln * rhd <= rhn * rld) by (nonlinear_arith)
        requires
            (rln * rhd) * (d1 * d2) <= (rhn * rld) * (d1 * d2),
            d1 > 0,
            d2 > 0,
    ;
}

/// `n1/d1 <= n2/d2` implies `round(·, Down) <= round(·, Up)`, including across
/// saturation, where I2 alone places a clamped endpoint on the right side.
/// This is what makes `QI::add`/`sub`/`mul` well-formed.
pub proof fn lemma_directed_round_order(n1: int, d1: int, n2: int, d2: int)
    requires
        d1 > 0,
        d2 > 0,
        n1 * d2 <= n2 * d1,
    ensures
        q_le(
            crate::round::round_frac(n1, d1, Dir::Down),
            crate::round::round_frac(n2, d2, Dir::Up),
        ),
{
    let rlo = crate::round::round_frac(n1, d1, Dir::Down);
    let rhi = crate::round::round_frac(n2, d2, Dir::Up);
    crate::round::lemma_round_frac_wf(n1, d1, Dir::Down);
    crate::round::lemma_round_frac_wf(n2, d2, Dir::Up);
    Rat::lemma_from_raw_spec_components((-(MAX_MAG as int)) as i64, 1);
    Rat::lemma_from_raw_spec_components(MAX_MAG, 1);
    // I2 alone. Every well-formed `Rat` lies in `[-MAX_MAG, MAX_MAG]`.
    assert(rlo.n() <= max_mag() * rlo.d()) by (nonlinear_arith)
        requires
            abs_int(rlo.n()) <= max_mag(),
            rlo.d() >= 1,
    ;
    assert(rhi.n() >= 0 - max_mag() * rhi.d()) by (nonlinear_arith)
        requires
            abs_int(rhi.n()) <= max_mag(),
            rhi.d() >= 1,
    ;
    if !crate::round::saturated(n1, d1) && !crate::round::saturated(n2, d2) {
        crate::round::lemma_r2_directed(n1, d1);
        crate::round::lemma_r2_directed(n2, d2);
        lemma_frac_chain_le(rlo.n(), rlo.d(), n1, d1, n2, d2, rhi.n(), rhi.d());
        assert(q_le(rlo, rhi));
    } else if crate::round::saturated(n1, d1) {
        assert(n1 != 0 && !magnitude_fits(n1, d1));
        if n1 < 0 {
            // `rlo` clamps to `-MAX_MAG`. That is a lower bound on every
            // well-formed `Rat`, and in particular on `rhi`.
            assert(rlo == Rat::from_raw_spec((-(MAX_MAG as int)) as i64, 1));
            assert(rlo.n() == 0 - max_mag() && rlo.d() == 1);
            assert(q_le(rlo, rhi)) by (nonlinear_arith)
                requires
                    rlo.n() == 0 - max_mag(),
                    rlo.d() == 1,
                    rhi.n() >= 0 - max_mag() * rhi.d(),
                    rhi.d() > 0,
            ;
        } else {
            // `rlo` clamps to `MAX_MAG`. `n1/d1 <= n2/d2` holds, and `n1/d1`
            // exceeds `MAX_MAG`. Thus `n2/d2` exceeds `MAX_MAG` too, `n2`
            // saturates the same way, and `rhi` clamps to the same value.
            assert(rlo == Rat::from_raw_spec(MAX_MAG, 1));
            assert(n2 > max_mag() * d2) by (nonlinear_arith)
                requires
                    n1 > max_mag() * d1,
                    n1 * d2 <= n2 * d1,
                    d1 > 0,
                    d2 > 0,
            ;
            assert(n2 != 0 && !magnitude_fits(n2, d2));
            assert(rhi == Rat::from_raw_spec(MAX_MAG, 1));
            assert(rlo.n() == max_mag() && rlo.d() == 1);
            assert(rhi.n() == max_mag() && rhi.d() == 1);
            assert(q_le(rlo, rhi)) by (nonlinear_arith)
                requires
                    rlo.n() == max_mag(),
                    rlo.d() == 1,
                    rhi.n() == max_mag(),
                    rhi.d() == 1,
            ;
        }
    } else {
        // `saturated(n2, d2)` and `!saturated(n1, d1)`.
        assert(n2 != 0 && !magnitude_fits(n2, d2));
        if n2 > 0 {
            // `rhi` clamps to `MAX_MAG`. That is an upper bound on every
            // well-formed `Rat`, and in particular on `rlo`.
            assert(rhi == Rat::from_raw_spec(MAX_MAG, 1));
            assert(rhi.n() == max_mag() && rhi.d() == 1);
            assert(q_le(rlo, rhi)) by (nonlinear_arith)
                requires
                    rlo.n() <= max_mag() * rlo.d(),
                    rlo.d() > 0,
                    rhi.n() == max_mag(),
                    rhi.d() == 1,
            ;
        } else {
            // `n2 < 0` here forces `n1/d1 <= n2/d2 < -MAX_MAG`. Then `n1`
            // saturates too, which contradicts `!saturated(n1, d1)`.
            assert(n1 < 0 - max_mag() * d1) by (nonlinear_arith)
                requires
                    n2 < 0 - max_mag() * d2,
                    n1 * d2 <= n2 * d1,
                    d1 > 0,
                    d2 > 0,
            ;
            assert(false);
        }
    }
}

// ---------------------------------------------------------------------------
// The multiplication corner rule
// ---------------------------------------------------------------------------

/// The smaller of the two fractions `n1/d1` and `n2/d2`, as a `(numerator,
/// denominator)` pair equal to whichever input is smaller. A tie keeps the
/// first input. This function only states the multiplication corner rule
/// without committing to a syntactically fixed winner among the four corners.
pub open spec fn frac_min(n1: int, d1: int, n2: int, d2: int) -> (int, int) {
    if n1 * d2 <= n2 * d1 {
        (n1, d1)
    } else {
        (n2, d2)
    }
}

/// The larger of the two fractions `n1/d1` and `n2/d2`. See [`frac_min`].
pub open spec fn frac_max(n1: int, d1: int, n2: int, d2: int) -> (int, int) {
    if n1 * d2 >= n2 * d1 {
        (n1, d1)
    } else {
        (n2, d2)
    }
}

/// `frac_min` is a lower bound on both of its inputs.
pub proof fn lemma_frac_min_le(n1: int, d1: int, n2: int, d2: int)
    requires
        d1 > 0,
        d2 > 0,
    ensures
        ({
            let (mn, md) = frac_min(n1, d1, n2, d2);
            &&& md > 0
            &&& mn * d1 <= n1 * md
            &&& mn * d2 <= n2 * md
        }),
{
}

/// `frac_max` is an upper bound on both of its inputs.
pub proof fn lemma_frac_max_ge(n1: int, d1: int, n2: int, d2: int)
    requires
        d1 > 0,
        d2 > 0,
    ensures
        ({
            let (mx, mxd) = frac_max(n1, d1, n2, d2);
            &&& mxd > 0
            &&& n1 * mxd <= mx * d1
            &&& n2 * mxd <= mx * d2
        }),
{
}

/// Fraction `<=` is transitive across three different denominators.
pub proof fn lemma_frac_le_trans(n1: int, d1: int, n2: int, d2: int, n3: int, d3: int)
    requires
        d1 > 0,
        d2 > 0,
        d3 > 0,
        n1 * d2 <= n2 * d1,
        n2 * d3 <= n3 * d2,
    ensures
        n1 * d3 <= n3 * d1,
{
    assert((n1 * d2) * d3 <= (n2 * d1) * d3) by (nonlinear_arith)
        requires
            n1 * d2 <= n2 * d1,
            d3 > 0,
    ;
    assert((n2 * d3) * d1 <= (n3 * d2) * d1) by (nonlinear_arith)
        requires
            n2 * d3 <= n3 * d2,
            d1 > 0,
    ;
    assert((n1 * d2) * d3 == (n1 * d3) * d2) by (nonlinear_arith);
    assert((n2 * d1) * d3 == (n2 * d3) * d1) by (nonlinear_arith);
    assert((n3 * d2) * d1 == (n3 * d1) * d2) by (nonlinear_arith);
    assert((n1 * d3) * d2 <= (n3 * d1) * d2);
    assert(n1 * d3 <= n3 * d1) by (nonlinear_arith)
        requires
            (n1 * d3) * d2 <= (n3 * d1) * d2,
            d2 > 0,
    ;
}

/// `frac_min` of four corners is a lower bound on all four.
pub proof fn lemma_frac_min4_le(n1: int, d1: int, n2: int, d2: int, n3: int, d3: int, n4: int, d4: int)
    requires
        d1 > 0,
        d2 > 0,
        d3 > 0,
        d4 > 0,
    ensures
        ({
            let m1 = frac_min(n1, d1, n2, d2);
            let m2 = frac_min(n3, d3, n4, d4);
            let (mn, md) = frac_min(m1.0, m1.1, m2.0, m2.1);
            &&& md > 0
            &&& mn * d1 <= n1 * md
            &&& mn * d2 <= n2 * md
            &&& mn * d3 <= n3 * md
            &&& mn * d4 <= n4 * md
        }),
{
    lemma_frac_min_le(n1, d1, n2, d2);
    lemma_frac_min_le(n3, d3, n4, d4);
    let m1 = frac_min(n1, d1, n2, d2);
    let m2 = frac_min(n3, d3, n4, d4);
    lemma_frac_min_le(m1.0, m1.1, m2.0, m2.1);
    let (mn, md) = frac_min(m1.0, m1.1, m2.0, m2.1);
    lemma_frac_le_trans(mn, md, m1.0, m1.1, n1, d1);
    lemma_frac_le_trans(mn, md, m1.0, m1.1, n2, d2);
    lemma_frac_le_trans(mn, md, m2.0, m2.1, n3, d3);
    lemma_frac_le_trans(mn, md, m2.0, m2.1, n4, d4);
}

/// `frac_max` of four corners is an upper bound on all four.
pub proof fn lemma_frac_max4_ge(n1: int, d1: int, n2: int, d2: int, n3: int, d3: int, n4: int, d4: int)
    requires
        d1 > 0,
        d2 > 0,
        d3 > 0,
        d4 > 0,
    ensures
        ({
            let m1 = frac_max(n1, d1, n2, d2);
            let m2 = frac_max(n3, d3, n4, d4);
            let (mx, mxd) = frac_max(m1.0, m1.1, m2.0, m2.1);
            &&& mxd > 0
            &&& n1 * mxd <= mx * d1
            &&& n2 * mxd <= mx * d2
            &&& n3 * mxd <= mx * d3
            &&& n4 * mxd <= mx * d4
        }),
{
    lemma_frac_max_ge(n1, d1, n2, d2);
    lemma_frac_max_ge(n3, d3, n4, d4);
    let m1 = frac_max(n1, d1, n2, d2);
    let m2 = frac_max(n3, d3, n4, d4);
    lemma_frac_max_ge(m1.0, m1.1, m2.0, m2.1);
    let (mx, mxd) = frac_max(m1.0, m1.1, m2.0, m2.1);
    lemma_frac_le_trans(n1, d1, m1.0, m1.1, mx, mxd);
    lemma_frac_le_trans(n2, d2, m1.0, m1.1, mx, mxd);
    lemma_frac_le_trans(n3, d3, m2.0, m2.1, mx, mxd);
    lemma_frac_le_trans(n4, d4, m2.0, m2.1, mx, mxd);
}

/// For `x` between `lo` and `hi`, `lo*c` and `hi*c` bracket the exact product
/// `x*c`. The sign of `c` decides which one is the lower bound and which the
/// upper bound. This is the one-variable fact under the corner rule. `x*y` is
/// affine in `x` for fixed `y`, and affine in `y` for fixed `x`. It is
/// therefore extremal at an endpoint of whichever variable stays free.
pub proof fn lemma_mul_scale_order(lo: Rat, hi: Rat, x: Rat, c: Rat)
    requires
        lo.wf(),
        hi.wf(),
        x.wf(),
        c.wf(),
        q_le(lo, x),
        q_le(x, hi),
    ensures
        c.n() >= 0 ==> (mul_n(lo, c) * prod_d(x, c) <= mul_n(x, c) * prod_d(lo, c)
            && mul_n(x, c) * prod_d(hi, c) <= mul_n(hi, c) * prod_d(x, c)),
        c.n() < 0 ==> (mul_n(hi, c) * prod_d(x, c) <= mul_n(x, c) * prod_d(hi, c)
            && mul_n(x, c) * prod_d(lo, c) <= mul_n(lo, c) * prod_d(x, c)),
{
    if c.n() >= 0 {
        assert((lo.n() * x.d()) * (c.n() * c.d()) <= (x.n() * lo.d()) * (c.n() * c.d()))
            by (nonlinear_arith)
            requires
                lo.n() * x.d() <= x.n() * lo.d(),
                c.n() >= 0,
                c.d() > 0,
        ;
        assert((lo.n() * x.d()) * (c.n() * c.d()) == mul_n(lo, c) * prod_d(x, c))
            by (nonlinear_arith);
        assert((x.n() * lo.d()) * (c.n() * c.d()) == mul_n(x, c) * prod_d(lo, c))
            by (nonlinear_arith);
        assert((x.n() * hi.d()) * (c.n() * c.d()) <= (hi.n() * x.d()) * (c.n() * c.d()))
            by (nonlinear_arith)
            requires
                x.n() * hi.d() <= hi.n() * x.d(),
                c.n() >= 0,
                c.d() > 0,
        ;
        assert((x.n() * hi.d()) * (c.n() * c.d()) == mul_n(x, c) * prod_d(hi, c))
            by (nonlinear_arith);
        assert((hi.n() * x.d()) * (c.n() * c.d()) == mul_n(hi, c) * prod_d(x, c))
            by (nonlinear_arith);
    } else {
        assert((x.n() * hi.d()) * (c.n() * c.d()) >= (hi.n() * x.d()) * (c.n() * c.d()))
            by (nonlinear_arith)
            requires
                x.n() * hi.d() <= hi.n() * x.d(),
                c.n() < 0,
                c.d() > 0,
        ;
        assert((x.n() * hi.d()) * (c.n() * c.d()) == mul_n(x, c) * prod_d(hi, c))
            by (nonlinear_arith);
        assert((hi.n() * x.d()) * (c.n() * c.d()) == mul_n(hi, c) * prod_d(x, c))
            by (nonlinear_arith);
        assert((lo.n() * x.d()) * (c.n() * c.d()) >= (x.n() * lo.d()) * (c.n() * c.d()))
            by (nonlinear_arith)
            requires
                lo.n() * x.d() <= x.n() * lo.d(),
                c.n() < 0,
                c.d() > 0,
        ;
        assert((lo.n() * x.d()) * (c.n() * c.d()) == mul_n(lo, c) * prod_d(x, c))
            by (nonlinear_arith);
        assert((x.n() * lo.d()) * (c.n() * c.d()) == mul_n(x, c) * prod_d(lo, c))
            by (nonlinear_arith);
    }
}

/// One corner is a lower bound on `x*y`: the sign of `y` selects the
/// `a`-endpoint, whose sign selects the `b`-endpoint.
pub proof fn lemma_mul_corner_lower(a: QI, b: QI, x: Rat, y: Rat)
    requires
        a.wf(),
        b.wf(),
        x.wf(),
        y.wf(),
        q_le(a.spec_lower(), x),
        q_le(x, a.spec_upper()),
        q_le(b.spec_lower(), y),
        q_le(y, b.spec_upper()),
    ensures
        (y.n() >= 0 && a.spec_lower().n() >= 0) ==> mul_n(a.spec_lower(), b.spec_lower()) * prod_d(x, y) <= mul_n(x, y) * prod_d(
            a.spec_lower(),
            b.spec_lower(),
        ),
        (y.n() >= 0 && a.spec_lower().n() < 0) ==> mul_n(a.spec_lower(), b.spec_upper()) * prod_d(x, y) <= mul_n(x, y) * prod_d(
            a.spec_lower(),
            b.spec_upper(),
        ),
        (y.n() < 0 && a.spec_upper().n() >= 0) ==> mul_n(a.spec_upper(), b.spec_lower()) * prod_d(x, y) <= mul_n(x, y) * prod_d(
            a.spec_upper(),
            b.spec_lower(),
        ),
        (y.n() < 0 && a.spec_upper().n() < 0) ==> mul_n(a.spec_upper(), b.spec_upper()) * prod_d(x, y) <= mul_n(x, y) * prod_d(
            a.spec_upper(),
            b.spec_upper(),
        ),
{
    crate::q::lemma_op_widths(a.lo, b.lo);
    crate::q::lemma_op_widths(a.lo, b.hi);
    crate::q::lemma_op_widths(a.hi, b.lo);
    crate::q::lemma_op_widths(a.hi, b.hi);
    crate::q::lemma_op_widths(a.lo, y);
    crate::q::lemma_op_widths(a.hi, y);
    crate::q::lemma_op_widths(x, y);
    lemma_mul_scale_order(a.lo, a.hi, x, y);
    if y.n() >= 0 {
        // `a.lo * y <= x * y`.
        if a.lo.n() >= 0 {
            lemma_mul_scale_order(b.lo, b.hi, y, a.lo);
            // `a.lo * b.lo <= a.lo * y`, via `mul_n`/`prod_d` symmetry.
            assert(mul_n(b.lo, a.lo) * prod_d(y, a.lo) <= mul_n(y, a.lo) * prod_d(b.lo, a.lo));
            assert(mul_n(b.lo, a.lo) == mul_n(a.lo, b.lo)) by (nonlinear_arith);
            assert(mul_n(y, a.lo) == mul_n(a.lo, y)) by (nonlinear_arith);
            assert(prod_d(y, a.lo) == prod_d(a.lo, y));
            assert(prod_d(b.lo, a.lo) == prod_d(a.lo, b.lo));
            lemma_frac_le_trans(
                mul_n(a.lo, b.lo),
                prod_d(a.lo, b.lo),
                mul_n(a.lo, y),
                prod_d(a.lo, y),
                mul_n(x, y),
                prod_d(x, y),
            );
        } else {
            lemma_mul_scale_order(b.lo, b.hi, y, a.lo);
            // `a.lo < 0`: `a.lo * b.hi <= a.lo * y`.
            assert(mul_n(b.hi, a.lo) * prod_d(y, a.lo) <= mul_n(y, a.lo) * prod_d(b.hi, a.lo));
            assert(mul_n(b.hi, a.lo) == mul_n(a.lo, b.hi)) by (nonlinear_arith);
            assert(mul_n(y, a.lo) == mul_n(a.lo, y)) by (nonlinear_arith);
            assert(prod_d(y, a.lo) == prod_d(a.lo, y));
            assert(prod_d(b.hi, a.lo) == prod_d(a.lo, b.hi));
            lemma_frac_le_trans(
                mul_n(a.lo, b.hi),
                prod_d(a.lo, b.hi),
                mul_n(a.lo, y),
                prod_d(a.lo, y),
                mul_n(x, y),
                prod_d(x, y),
            );
        }
    } else {
        // `a.hi * y <= x * y`.
        if a.hi.n() >= 0 {
            lemma_mul_scale_order(b.lo, b.hi, y, a.hi);
            assert(mul_n(b.lo, a.hi) * prod_d(y, a.hi) <= mul_n(y, a.hi) * prod_d(b.lo, a.hi));
            assert(mul_n(b.lo, a.hi) == mul_n(a.hi, b.lo)) by (nonlinear_arith);
            assert(mul_n(y, a.hi) == mul_n(a.hi, y)) by (nonlinear_arith);
            assert(prod_d(y, a.hi) == prod_d(a.hi, y));
            assert(prod_d(b.lo, a.hi) == prod_d(a.hi, b.lo));
            lemma_frac_le_trans(
                mul_n(a.hi, b.lo),
                prod_d(a.hi, b.lo),
                mul_n(a.hi, y),
                prod_d(a.hi, y),
                mul_n(x, y),
                prod_d(x, y),
            );
        } else {
            lemma_mul_scale_order(b.lo, b.hi, y, a.hi);
            assert(mul_n(b.hi, a.hi) * prod_d(y, a.hi) <= mul_n(y, a.hi) * prod_d(b.hi, a.hi));
            assert(mul_n(b.hi, a.hi) == mul_n(a.hi, b.hi)) by (nonlinear_arith);
            assert(mul_n(y, a.hi) == mul_n(a.hi, y)) by (nonlinear_arith);
            assert(prod_d(y, a.hi) == prod_d(a.hi, y));
            assert(prod_d(b.hi, a.hi) == prod_d(a.hi, b.hi));
            lemma_frac_le_trans(
                mul_n(a.hi, b.hi),
                prod_d(a.hi, b.hi),
                mul_n(a.hi, y),
                prod_d(a.hi, y),
                mul_n(x, y),
                prod_d(x, y),
            );
        }
    }
}

/// One of the four corners is an upper bound on the exact product `x*y`. This
/// lemma is the mirror image of [`lemma_mul_corner_lower`].
pub proof fn lemma_mul_corner_upper(a: QI, b: QI, x: Rat, y: Rat)
    requires
        a.wf(),
        b.wf(),
        x.wf(),
        y.wf(),
        q_le(a.spec_lower(), x),
        q_le(x, a.spec_upper()),
        q_le(b.spec_lower(), y),
        q_le(y, b.spec_upper()),
    ensures
        (y.n() >= 0 && a.spec_upper().n() >= 0) ==> mul_n(x, y) * prod_d(a.spec_upper(), b.spec_upper()) <= mul_n(
            a.spec_upper(),
            b.spec_upper(),
        ) * prod_d(x, y),
        (y.n() >= 0 && a.spec_upper().n() < 0) ==> mul_n(x, y) * prod_d(a.spec_upper(), b.spec_lower()) <= mul_n(
            a.spec_upper(),
            b.spec_lower(),
        ) * prod_d(x, y),
        (y.n() < 0 && a.spec_lower().n() >= 0) ==> mul_n(x, y) * prod_d(a.spec_lower(), b.spec_upper()) <= mul_n(
            a.spec_lower(),
            b.spec_upper(),
        ) * prod_d(x, y),
        (y.n() < 0 && a.spec_lower().n() < 0) ==> mul_n(x, y) * prod_d(a.spec_lower(), b.spec_lower()) <= mul_n(
            a.spec_lower(),
            b.spec_lower(),
        ) * prod_d(x, y),
{
    crate::q::lemma_op_widths(a.lo, b.lo);
    crate::q::lemma_op_widths(a.lo, b.hi);
    crate::q::lemma_op_widths(a.hi, b.lo);
    crate::q::lemma_op_widths(a.hi, b.hi);
    crate::q::lemma_op_widths(a.lo, y);
    crate::q::lemma_op_widths(a.hi, y);
    crate::q::lemma_op_widths(x, y);
    lemma_mul_scale_order(a.lo, a.hi, x, y);
    if y.n() >= 0 {
        // `x * y <= a.hi * y`.
        if a.hi.n() >= 0 {
            lemma_mul_scale_order(b.lo, b.hi, y, a.hi);
            // `a.hi * y <= a.hi * b.hi`.
            assert(mul_n(y, a.hi) * prod_d(b.hi, a.hi) <= mul_n(b.hi, a.hi) * prod_d(y, a.hi));
            assert(mul_n(b.hi, a.hi) == mul_n(a.hi, b.hi)) by (nonlinear_arith);
            assert(mul_n(y, a.hi) == mul_n(a.hi, y)) by (nonlinear_arith);
            assert(prod_d(y, a.hi) == prod_d(a.hi, y));
            assert(prod_d(b.hi, a.hi) == prod_d(a.hi, b.hi));
            lemma_frac_le_trans(
                mul_n(x, y),
                prod_d(x, y),
                mul_n(a.hi, y),
                prod_d(a.hi, y),
                mul_n(a.hi, b.hi),
                prod_d(a.hi, b.hi),
            );
        } else {
            lemma_mul_scale_order(b.lo, b.hi, y, a.hi);
            // `a.hi < 0`: `a.hi * y <= a.hi * b.lo`.
            assert(mul_n(y, a.hi) * prod_d(b.lo, a.hi) <= mul_n(b.lo, a.hi) * prod_d(y, a.hi));
            assert(mul_n(b.lo, a.hi) == mul_n(a.hi, b.lo)) by (nonlinear_arith);
            assert(mul_n(y, a.hi) == mul_n(a.hi, y)) by (nonlinear_arith);
            assert(prod_d(y, a.hi) == prod_d(a.hi, y));
            assert(prod_d(b.lo, a.hi) == prod_d(a.hi, b.lo));
            lemma_frac_le_trans(
                mul_n(x, y),
                prod_d(x, y),
                mul_n(a.hi, y),
                prod_d(a.hi, y),
                mul_n(a.hi, b.lo),
                prod_d(a.hi, b.lo),
            );
        }
    } else {
        // `x * y <= a.lo * y`.
        if a.lo.n() >= 0 {
            lemma_mul_scale_order(b.lo, b.hi, y, a.lo);
            assert(mul_n(y, a.lo) * prod_d(b.hi, a.lo) <= mul_n(b.hi, a.lo) * prod_d(y, a.lo));
            assert(mul_n(b.hi, a.lo) == mul_n(a.lo, b.hi)) by (nonlinear_arith);
            assert(mul_n(y, a.lo) == mul_n(a.lo, y)) by (nonlinear_arith);
            assert(prod_d(y, a.lo) == prod_d(a.lo, y));
            assert(prod_d(b.hi, a.lo) == prod_d(a.lo, b.hi));
            lemma_frac_le_trans(
                mul_n(x, y),
                prod_d(x, y),
                mul_n(a.lo, y),
                prod_d(a.lo, y),
                mul_n(a.lo, b.hi),
                prod_d(a.lo, b.hi),
            );
        } else {
            lemma_mul_scale_order(b.lo, b.hi, y, a.lo);
            assert(mul_n(y, a.lo) * prod_d(b.lo, a.lo) <= mul_n(b.lo, a.lo) * prod_d(y, a.lo));
            assert(mul_n(b.lo, a.lo) == mul_n(a.lo, b.lo)) by (nonlinear_arith);
            assert(mul_n(y, a.lo) == mul_n(a.lo, y)) by (nonlinear_arith);
            assert(prod_d(y, a.lo) == prod_d(a.lo, y));
            assert(prod_d(b.lo, a.lo) == prod_d(a.lo, b.lo));
            lemma_frac_le_trans(
                mul_n(x, y),
                prod_d(x, y),
                mul_n(a.lo, y),
                prod_d(a.lo, y),
                mul_n(a.lo, b.lo),
                prod_d(a.lo, b.lo),
            );
        }
    }
}

/// The corner rule: `x*y` lies between the min and max of the four exact
/// corner products, for every sign pattern.
pub proof fn theorem_interval_mul_contains(a: QI, b: QI, x: Rat, y: Rat)
    requires
        a.wf(),
        b.wf(),
        x.wf(),
        y.wf(),
        q_le(a.spec_lower(), x),
        q_le(x, a.spec_upper()),
        q_le(b.spec_lower(), y),
        q_le(y, b.spec_upper()),
    ensures
        ({
            let (mn, md) = frac_min(
                frac_min(
                    mul_n(a.spec_lower(), b.spec_lower()),
                    prod_d(a.spec_lower(), b.spec_lower()),
                    mul_n(a.spec_lower(), b.spec_upper()),
                    prod_d(a.spec_lower(), b.spec_upper()),
                ).0,
                frac_min(
                    mul_n(a.spec_lower(), b.spec_lower()),
                    prod_d(a.spec_lower(), b.spec_lower()),
                    mul_n(a.spec_lower(), b.spec_upper()),
                    prod_d(a.spec_lower(), b.spec_upper()),
                ).1,
                frac_min(
                    mul_n(a.spec_upper(), b.spec_lower()),
                    prod_d(a.spec_upper(), b.spec_lower()),
                    mul_n(a.spec_upper(), b.spec_upper()),
                    prod_d(a.spec_upper(), b.spec_upper()),
                ).0,
                frac_min(
                    mul_n(a.spec_upper(), b.spec_lower()),
                    prod_d(a.spec_upper(), b.spec_lower()),
                    mul_n(a.spec_upper(), b.spec_upper()),
                    prod_d(a.spec_upper(), b.spec_upper()),
                ).1,
            );
            mn * prod_d(x, y) <= mul_n(x, y) * md
        }),
        ({
            let (mx, mxd) = frac_max(
                frac_max(
                    mul_n(a.spec_lower(), b.spec_lower()),
                    prod_d(a.spec_lower(), b.spec_lower()),
                    mul_n(a.spec_lower(), b.spec_upper()),
                    prod_d(a.spec_lower(), b.spec_upper()),
                ).0,
                frac_max(
                    mul_n(a.spec_lower(), b.spec_lower()),
                    prod_d(a.spec_lower(), b.spec_lower()),
                    mul_n(a.spec_lower(), b.spec_upper()),
                    prod_d(a.spec_lower(), b.spec_upper()),
                ).1,
                frac_max(
                    mul_n(a.spec_upper(), b.spec_lower()),
                    prod_d(a.spec_upper(), b.spec_lower()),
                    mul_n(a.spec_upper(), b.spec_upper()),
                    prod_d(a.spec_upper(), b.spec_upper()),
                ).0,
                frac_max(
                    mul_n(a.spec_upper(), b.spec_lower()),
                    prod_d(a.spec_upper(), b.spec_lower()),
                    mul_n(a.spec_upper(), b.spec_upper()),
                    prod_d(a.spec_upper(), b.spec_upper()),
                ).1,
            );
            mul_n(x, y) * mxd <= mx * prod_d(x, y)
        }),
{
    crate::q::lemma_op_widths(a.lo, b.lo);
    crate::q::lemma_op_widths(a.lo, b.hi);
    crate::q::lemma_op_widths(a.hi, b.lo);
    crate::q::lemma_op_widths(a.hi, b.hi);
    crate::q::lemma_op_widths(x, y);
    lemma_frac_min4_le(
        mul_n(a.lo, b.lo),
        prod_d(a.lo, b.lo),
        mul_n(a.lo, b.hi),
        prod_d(a.lo, b.hi),
        mul_n(a.hi, b.lo),
        prod_d(a.hi, b.lo),
        mul_n(a.hi, b.hi),
        prod_d(a.hi, b.hi),
    );
    lemma_frac_max4_ge(
        mul_n(a.lo, b.lo),
        prod_d(a.lo, b.lo),
        mul_n(a.lo, b.hi),
        prod_d(a.lo, b.hi),
        mul_n(a.hi, b.lo),
        prod_d(a.hi, b.lo),
        mul_n(a.hi, b.hi),
        prod_d(a.hi, b.hi),
    );
    lemma_mul_corner_lower(a, b, x, y);
    lemma_mul_corner_upper(a, b, x, y);
    let m1 = frac_min(
        mul_n(a.lo, b.lo),
        prod_d(a.lo, b.lo),
        mul_n(a.lo, b.hi),
        prod_d(a.lo, b.hi),
    );
    let m2 = frac_min(
        mul_n(a.hi, b.lo),
        prod_d(a.hi, b.lo),
        mul_n(a.hi, b.hi),
        prod_d(a.hi, b.hi),
    );
    let (mn, md) = frac_min(m1.0, m1.1, m2.0, m2.1);
    let mx1 = frac_max(
        mul_n(a.lo, b.lo),
        prod_d(a.lo, b.lo),
        mul_n(a.lo, b.hi),
        prod_d(a.lo, b.hi),
    );
    let mx2 = frac_max(
        mul_n(a.hi, b.lo),
        prod_d(a.hi, b.lo),
        mul_n(a.hi, b.hi),
        prod_d(a.hi, b.hi),
    );
    let (mx, mxd) = frac_max(mx1.0, mx1.1, mx2.0, mx2.1);
    // Chain `mn <= winning_corner <= x*y` and `x*y <= winning_corner <= mx`,
    // for whichever corner each helper returns.
    if y.n() >= 0 && a.lo.n() >= 0 {
        lemma_frac_le_trans(mn, md, mul_n(a.lo, b.lo), prod_d(a.lo, b.lo), mul_n(x, y), prod_d(x, y));
    } else if y.n() >= 0 {
        lemma_frac_le_trans(mn, md, mul_n(a.lo, b.hi), prod_d(a.lo, b.hi), mul_n(x, y), prod_d(x, y));
    } else if a.hi.n() >= 0 {
        lemma_frac_le_trans(mn, md, mul_n(a.hi, b.lo), prod_d(a.hi, b.lo), mul_n(x, y), prod_d(x, y));
    } else {
        lemma_frac_le_trans(mn, md, mul_n(a.hi, b.hi), prod_d(a.hi, b.hi), mul_n(x, y), prod_d(x, y));
    }
    if y.n() >= 0 && a.hi.n() >= 0 {
        lemma_frac_le_trans(mul_n(x, y), prod_d(x, y), mul_n(a.hi, b.hi), prod_d(a.hi, b.hi), mx, mxd);
    } else if y.n() >= 0 {
        lemma_frac_le_trans(mul_n(x, y), prod_d(x, y), mul_n(a.hi, b.lo), prod_d(a.hi, b.lo), mx, mxd);
    } else if a.lo.n() >= 0 {
        lemma_frac_le_trans(mul_n(x, y), prod_d(x, y), mul_n(a.lo, b.hi), prod_d(a.lo, b.hi), mx, mxd);
    } else {
        lemma_frac_le_trans(mul_n(x, y), prod_d(x, y), mul_n(a.lo, b.lo), prod_d(a.lo, b.lo), mx, mxd);
    }
}

} // verus!
