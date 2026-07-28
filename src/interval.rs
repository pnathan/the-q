//! `QI` — a rational interval built on the directed rounding modes (M6).
//!
//! This is why R2 exists. An interval `[lo, hi]` that brackets a true value
//! keeps bracketing it if every lower endpoint is computed with [`Dir::Down`]
//! and every upper endpoint with [`Dir::Up`] — and R2 says exactly that those
//! modes never cross the exact value. So the containment theorem needs **no new
//! rounding proofs**; it is a corollary of R2 plus the monotonicity of the
//! underlying rational operations.
//!
//! The interval layer is the honest answer to "how much did rounding cost me on
//! *this* computation": instead of a worst-case bound, the width of the result
//! is the measured answer.

use verus_builtin_macros::verus;

#[allow(unused_imports)]
use verus_builtin::*;
#[allow(unused_imports)]
use vstd::prelude::*;

#[allow(unused_imports)]
use crate::model::*;
#[allow(unused_imports)]
use crate::q::*;
use crate::types::{Dir, Q};

verus! {

/// A closed rational interval `[lo, hi]`.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct QI {
    /// The lower endpoint. Always computed with [`Dir::Down`].
    pub lo: Q,
    /// The upper endpoint. Always computed with [`Dir::Up`].
    pub hi: Q,
}

impl QI {
    /// The interval invariant: both endpoints well-formed and correctly
    /// ordered.
    pub open spec fn wf(self) -> bool {
        &&& self.lo.wf()
        &&& self.hi.wf()
        &&& q_le(self.lo, self.hi)
    }

    /// The degenerate interval `[a, a]`.
    pub fn exact(a: Q) -> (r: QI)
        requires
            a.wf(),
        ensures
            r.wf(),
            r.lo == a,
            r.hi == a,
    {
        QI { lo: a, hi: a }
    }

    /// `[lo, hi]`, requiring the endpoints to be ordered.
    pub fn new(lo: Q, hi: Q) -> (r: QI)
        requires
            lo.wf(),
            hi.wf(),
            q_le(lo, hi),
        ensures
            r.wf(),
            r.lo == lo,
            r.hi == hi,
    {
        QI { lo, hi }
    }

    /// Whether `x` lies inside the interval.
    pub fn contains(&self, x: Q) -> (r: bool)
        requires
            self.wf(),
            x.wf(),
        ensures
            r <==> (q_le(self.lo, x) && q_le(x, self.hi)),
    {
        Q::le(self.lo, x) && Q::le(x, self.hi)
    }

    /// `hi - lo`: how much precision the computation actually lost. Zero means
    /// the whole computation stayed on the exact path.
    pub fn width(&self) -> (r: Q)
        requires
            self.wf(),
        ensures
            r.wf(),
    {
        Q::sub_dir(self.hi, self.lo, Dir::Up)
    }

    /// Interval addition: `[a.lo + b.lo, a.hi + b.hi]` with outward rounding.
    pub fn add(a: QI, b: QI) -> (r: QI)
        requires
            a.wf(),
            b.wf(),
        ensures
            r.lo.wf(),
            r.hi.wf(),
            !crate::round::saturated(add_n(a.lo, b.lo), prod_d(a.lo, b.lo)) ==> q_le_frac(
                r.lo,
                add_n(a.lo, b.lo),
                prod_d(a.lo, b.lo),
            ),
            !crate::round::saturated(add_n(a.hi, b.hi), prod_d(a.hi, b.hi)) ==> q_ge_frac(
                r.hi,
                add_n(a.hi, b.hi),
                prod_d(a.hi, b.hi),
            ),
    {
        let lo = Q::add_dir(a.lo, b.lo, Dir::Down);
        let hi = Q::add_dir(a.hi, b.hi, Dir::Up);
        proof {
            crate::q::lemma_op_widths(a.lo, b.lo);
            crate::q::lemma_op_widths(a.hi, b.hi);
            if !crate::round::saturated(add_n(a.lo, b.lo), prod_d(a.lo, b.lo)) {
                crate::round::lemma_r2_directed(add_n(a.lo, b.lo), prod_d(a.lo, b.lo));
            }
            if !crate::round::saturated(add_n(a.hi, b.hi), prod_d(a.hi, b.hi)) {
                crate::round::lemma_r2_directed(add_n(a.hi, b.hi), prod_d(a.hi, b.hi));
            }
        }
        QI { lo, hi }
    }

    /// Interval subtraction: `[a.lo - b.hi, a.hi - b.lo]` with outward
    /// rounding.
    pub fn sub(a: QI, b: QI) -> (r: QI)
        requires
            a.wf(),
            b.wf(),
        ensures
            r.lo.wf(),
            r.hi.wf(),
            !crate::round::saturated(sub_n(a.lo, b.hi), prod_d(a.lo, b.hi)) ==> q_le_frac(
                r.lo,
                sub_n(a.lo, b.hi),
                prod_d(a.lo, b.hi),
            ),
            !crate::round::saturated(sub_n(a.hi, b.lo), prod_d(a.hi, b.lo)) ==> q_ge_frac(
                r.hi,
                sub_n(a.hi, b.lo),
                prod_d(a.hi, b.lo),
            ),
    {
        let lo = Q::sub_dir(a.lo, b.hi, Dir::Down);
        let hi = Q::sub_dir(a.hi, b.lo, Dir::Up);
        proof {
            crate::q::lemma_op_widths(a.lo, b.hi);
            crate::q::lemma_op_widths(a.hi, b.lo);
            if !crate::round::saturated(sub_n(a.lo, b.hi), prod_d(a.lo, b.hi)) {
                crate::round::lemma_r2_directed(sub_n(a.lo, b.hi), prod_d(a.lo, b.hi));
            }
            if !crate::round::saturated(sub_n(a.hi, b.lo), prod_d(a.hi, b.lo)) {
                crate::round::lemma_r2_directed(sub_n(a.hi, b.lo), prod_d(a.hi, b.lo));
            }
        }
        QI { lo, hi }
    }

    /// Interval negation: `[-hi, -lo]`. Exact.
    pub fn neg(a: QI) -> (r: QI)
        requires
            a.wf(),
        ensures
            r.wf(),
            r.lo.n() == -a.hi.n(),
            r.hi.n() == -a.lo.n(),
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

    /// Interval multiplication: the four corner products, outward rounded.
    ///
    /// The corner rule is the textbook one and is correct for every sign
    /// pattern, which is why no case analysis on signs appears here.
    pub fn mul(a: QI, b: QI) -> (r: QI)
        requires
            a.wf(),
            b.wf(),
        ensures
            r.lo.wf(),
            r.hi.wf(),
    {
        let ll_lo = Q::mul_dir(a.lo, b.lo, Dir::Down);
        let lh_lo = Q::mul_dir(a.lo, b.hi, Dir::Down);
        let hl_lo = Q::mul_dir(a.hi, b.lo, Dir::Down);
        let hh_lo = Q::mul_dir(a.hi, b.hi, Dir::Down);
        let ll_hi = Q::mul_dir(a.lo, b.lo, Dir::Up);
        let lh_hi = Q::mul_dir(a.lo, b.hi, Dir::Up);
        let hl_hi = Q::mul_dir(a.hi, b.lo, Dir::Up);
        let hh_hi = Q::mul_dir(a.hi, b.hi, Dir::Up);
        let lo = Q::min(Q::min(ll_lo, lh_lo), Q::min(hl_lo, hh_lo));
        let hi = Q::max(Q::max(ll_hi, lh_hi), Q::max(hl_hi, hh_hi));
        QI { lo, hi }
    }

    /// The union hull of two intervals.
    pub fn hull(a: QI, b: QI) -> (r: QI)
        requires
            a.wf(),
            b.wf(),
        ensures
            r.wf(),
    {
        let lo = Q::min(a.lo, b.lo);
        let hi = Q::max(a.hi, b.hi);
        proof {
            crate::q::lemma_le_trans(lo, a.lo, a.hi);
            crate::q::lemma_le_trans(lo, a.hi, hi);
        }
        QI { lo, hi }
    }
}

/// **The containment theorem.** If the inputs bracket their true values, the
/// interval sum brackets the true sum.
///
/// This is a direct corollary of R2 — the point of having directed modes at
/// all.
pub proof fn theorem_interval_add_contains(a: QI, b: QI, x: Q, y: Q)
    requires
        a.wf(),
        b.wf(),
        x.wf(),
        y.wf(),
        q_le(a.lo, x),
        q_le(x, a.hi),
        q_le(b.lo, y),
        q_le(y, b.hi),
    ensures
        // The exact sum of x and y lies between the exact sums of the
        // endpoints, so after outward rounding it lies inside `QI::add(a, b)`.
        add_n(a.lo, b.lo) * prod_d(x, y) <= add_n(x, y) * prod_d(a.lo, b.lo),
        add_n(x, y) * prod_d(a.hi, b.hi) <= add_n(a.hi, b.hi) * prod_d(x, y),
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

/// Adding two ordered pairs of fractions preserves the order.
///
/// Broken into four small steps rather than handed to `nonlinear_arith` whole:
/// scale each hypothesis by the other pair's positive denominators, then two
/// ring identities line the sums up with the goal. The solver does badly on the
/// combined form and fine on these.
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
    // Distribution and rearrangement are separated deliberately. Handed the
    // combined identity, the solver has to discover the factorisation itself
    // and burns through its budget; given distribution as its own step, each
    // remaining goal is an associativity/commutativity shuffle of a four-factor
    // product, which it normalises for free.
    assert((an * bd + bn * ad) * (xd * yd) == (an * bd) * (xd * yd) + (bn * ad) * (xd * yd))
        by (nonlinear_arith);
    assert((an * bd) * (xd * yd) == (an * xd) * (bd * yd)) by (nonlinear_arith);
    assert((bn * ad) * (xd * yd) == (bn * yd) * (ad * xd)) by (nonlinear_arith);
    assert((xn * yd + yn * xd) * (ad * bd) == (xn * yd) * (ad * bd) + (yn * xd) * (ad * bd))
        by (nonlinear_arith);
    assert((xn * yd) * (ad * bd) == (xn * ad) * (bd * yd)) by (nonlinear_arith);
    assert((yn * xd) * (ad * bd) == (yn * bd) * (ad * xd)) by (nonlinear_arith);
}

} // verus!
