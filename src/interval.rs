//! `QI` — a rational interval built on the directed rounding modes (M6).
//!
//! This module is the reason R2 exists. An interval `[lo, hi]` that brackets a
//! true value keeps bracketing it when every lower endpoint uses [`Dir::Down`]
//! and every upper endpoint uses [`Dir::Up`]. R2 states exactly that those
//! modes never cross the exact value. The containment theorem therefore needs
//! **no new rounding proofs**. It is a corollary of R2 plus the monotonicity of
//! the underlying rational operations.
//!
//! The interval layer measures the rounding cost of one specific computation.
//! The width of the result is that measurement, rather than a worst-case
//! bound.

use verus_builtin_macros::verus;

#[allow(unused_imports)]
use verus_builtin::*;
#[allow(unused_imports)]
use vstd::prelude::*;

#[allow(unused_imports)]
use crate::model::*;
#[allow(unused_imports)]
use crate::q::*;
#[allow(unused_imports)]
use crate::types::MAX_MAG;
use crate::types::{Dir, Rat};

verus! {

/// A closed rational interval `[lo, hi]`.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct QI {
    /// The lower endpoint. Always computed with [`Dir::Down`].
    pub lo: Rat,
    /// The upper endpoint. Always computed with [`Dir::Up`].
    pub hi: Rat,
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
    pub fn exact(a: Rat) -> (r: QI)
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
    pub fn new(lo: Rat, hi: Rat) -> (r: QI)
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
    pub fn contains(&self, x: Rat) -> (r: bool)
        requires
            self.wf(),
            x.wf(),
        ensures
            r <==> (q_le(self.lo, x) && q_le(x, self.hi)),
    {
        Rat::le(self.lo, x) && Rat::le(x, self.hi)
    }

    /// `hi - lo`. This is the precision the computation loses. Zero means the
    /// whole computation stays on the exact path.
    pub fn width(&self) -> (r: Rat)
        requires
            self.wf(),
        ensures
            r.wf(),
            !crate::round::saturated(sub_n(self.hi, self.lo), prod_d(self.hi, self.lo)) ==> q_ge_frac(
                r,
                sub_n(self.hi, self.lo),
                prod_d(self.hi, self.lo),
            ),
    {
        let r = Rat::sub_dir(self.hi, self.lo, Dir::Up);
        proof {
            crate::q::lemma_op_widths(self.hi, self.lo);
            if !crate::round::saturated(sub_n(self.hi, self.lo), prod_d(self.hi, self.lo)) {
                crate::round::lemma_r2_directed(sub_n(self.hi, self.lo), prod_d(self.hi, self.lo));
            }
        }
        r
    }

    /// Interval addition: `[a.lo + b.lo, a.hi + b.hi]` with outward rounding.
    ///
    /// `r.wf()` lets the result compose with the next operation inside
    /// verified code. It is a corollary of R2 plus the fact that `a.wf()` and
    /// `b.wf()` order the exact endpoint sums. See
    /// `lemma_directed_round_order`.
    pub fn add(a: QI, b: QI) -> (r: QI)
        requires
            a.wf(),
            b.wf(),
        ensures
            r.wf(),
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

    /// Interval subtraction: `[a.lo - b.hi, a.hi - b.lo]` with outward
    /// rounding.
    ///
    /// `r.wf()` holds for the same reason as in [`QI::add`]. The exact
    /// lo-difference never exceeds the exact hi-difference, because
    /// `a.lo - b.hi` is `a.lo + (-b.hi)` and `-b.hi <= -b.lo` follows from
    /// `b.wf()`.
    pub fn sub(a: QI, b: QI) -> (r: QI)
        requires
            a.wf(),
            b.wf(),
        ensures
            r.wf(),
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
    /// The corner rule states that the extremal corner products bracket the
    /// exact product for every sign pattern. `theorem_interval_mul_contains`
    /// proves it. `r.wf()` needs none of that case analysis. `lo` is the min
    /// and `hi` the max over all four *rounded* corners. Thus any single
    /// corner's `Down`/`Up` pair, such as the `ll` one, already chains
    /// `lo <= ll_lo <= ll_hi <= hi`.
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
    pub fn hull(a: QI, b: QI) -> (r: QI)
        requires
            a.wf(),
            b.wf(),
        ensures
            r.wf(),
            r.lo == a.lo || r.lo == b.lo,
            r.hi == a.hi || r.hi == b.hi,
            q_le(r.lo, a.lo),
            q_le(r.lo, b.lo),
            q_le(a.hi, r.hi),
            q_le(b.hi, r.hi),
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
        q_le(a.lo, x),
        q_le(x, a.hi),
        q_le(b.lo, y),
        q_le(y, b.hi),
    ensures
        // The exact sum of x and y lies between the exact sums of the
        // endpoints. After outward rounding it therefore lies inside
        // `QI::add(a, b)`.
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

/// **The containment theorem for subtraction.** If the inputs bracket their
/// true values, the interval difference brackets the true difference.
///
/// `a.lo - b.hi` is `a.lo + (-b.hi)`. This is therefore the same corollary of
/// R2 as [`theorem_interval_add_contains`], applied to `a.lo`/`a.hi` and the
/// negation of `b.hi`/`b.lo`.
pub proof fn theorem_interval_sub_contains(a: QI, b: QI, x: Rat, y: Rat)
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
        // The exact difference of x and y lies between the exact differences
        // of the endpoints. After outward rounding it therefore lies inside
        // `QI::sub(a, b)`.
        sub_n(a.lo, b.hi) * prod_d(x, y) <= sub_n(x, y) * prod_d(a.lo, b.hi),
        sub_n(x, y) * prod_d(a.hi, b.lo) <= sub_n(a.hi, b.lo) * prod_d(x, y),
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
///
/// The proof uses four small steps instead of one whole `nonlinear_arith`
/// goal. It scales each hypothesis by the other pair's positive denominators.
/// Two ring identities then line the sums up with the goal. The solver handles
/// these steps well and the combined form badly.
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

/// Chains three fraction comparisons across three different denominators:
/// `rl <= n1/d1 <= n2/d2 <= rh` implies `rl <= rh`.
///
/// This is [`crate::q::lemma_le_trans`] generalised off `Rat`. The middle link
/// is a raw fraction inequality, as [`lemma_add_endpoint_order`] produces, not
/// another well-formed `Rat`. The proof therefore redoes the cancellation by
/// hand.
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

/// If the exact `n1/d1 <= n2/d2`, then rounding the first `Down` and the
/// second `Up` preserves the order. This holds **even across saturation**,
/// where R2 alone does not apply.
///
/// This lemma makes `QI::add`, `QI::sub` and, through a single corner,
/// `QI::mul` produce a well-formed result. Each of them computes its `lo` and
/// `hi` endpoints by rounding two *ordered* exact fractions in opposite
/// directions. This lemma carries the transition from ordered inputs to
/// ordered rounded outputs, whether or not either side saturates.
///
/// The saturated cases use I2 alone. Every well-formed `Rat` lies in
/// `[-MAX_MAG, MAX_MAG]`. A clamped endpoint therefore lies on the correct
/// side of whatever the other endpoint rounds to.
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
            assert(rlo == Rat { num: (-(MAX_MAG as int)) as i64, den: 1 });
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
            assert(rlo == Rat { num: MAX_MAG, den: 1 });
            assert(n2 > max_mag() * d2) by (nonlinear_arith)
                requires
                    n1 > max_mag() * d1,
                    n1 * d2 <= n2 * d1,
                    d1 > 0,
                    d2 > 0,
            ;
            assert(n2 != 0 && !magnitude_fits(n2, d2));
            assert(rhi == Rat { num: MAX_MAG, den: 1 });
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
            assert(rhi == Rat { num: MAX_MAG, den: 1 });
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

/// One of the four corners is a lower bound on the exact product `x*y`, for
/// `x` in `a`'s range and `y` in `b`'s range.
///
/// The winning corner is the textbook one. The sign of `y` selects the
/// `a`-endpoint. The sign of that `a`-endpoint then selects the `b`-endpoint.
/// The proof applies [`lemma_mul_scale_order`] twice and chains the results
/// through [`lemma_frac_le_trans`].
pub proof fn lemma_mul_corner_lower(a: QI, b: QI, x: Rat, y: Rat)
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
        (y.n() >= 0 && a.lo.n() >= 0) ==> mul_n(a.lo, b.lo) * prod_d(x, y) <= mul_n(x, y) * prod_d(
            a.lo,
            b.lo,
        ),
        (y.n() >= 0 && a.lo.n() < 0) ==> mul_n(a.lo, b.hi) * prod_d(x, y) <= mul_n(x, y) * prod_d(
            a.lo,
            b.hi,
        ),
        (y.n() < 0 && a.hi.n() >= 0) ==> mul_n(a.hi, b.lo) * prod_d(x, y) <= mul_n(x, y) * prod_d(
            a.hi,
            b.lo,
        ),
        (y.n() < 0 && a.hi.n() < 0) ==> mul_n(a.hi, b.hi) * prod_d(x, y) <= mul_n(x, y) * prod_d(
            a.hi,
            b.hi,
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
            assert(mul_n(b.lo, a.lo) == mul_n(a.lo, b.lo));
            assert(mul_n(y, a.lo) == mul_n(a.lo, y));
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
            assert(mul_n(b.hi, a.lo) == mul_n(a.lo, b.hi));
            assert(mul_n(y, a.lo) == mul_n(a.lo, y));
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
            assert(mul_n(b.lo, a.hi) == mul_n(a.hi, b.lo));
            assert(mul_n(y, a.hi) == mul_n(a.hi, y));
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
            assert(mul_n(b.hi, a.hi) == mul_n(a.hi, b.hi));
            assert(mul_n(y, a.hi) == mul_n(a.hi, y));
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
        q_le(a.lo, x),
        q_le(x, a.hi),
        q_le(b.lo, y),
        q_le(y, b.hi),
    ensures
        (y.n() >= 0 && a.hi.n() >= 0) ==> mul_n(x, y) * prod_d(a.hi, b.hi) <= mul_n(
            a.hi,
            b.hi,
        ) * prod_d(x, y),
        (y.n() >= 0 && a.hi.n() < 0) ==> mul_n(x, y) * prod_d(a.hi, b.lo) <= mul_n(
            a.hi,
            b.lo,
        ) * prod_d(x, y),
        (y.n() < 0 && a.lo.n() >= 0) ==> mul_n(x, y) * prod_d(a.lo, b.hi) <= mul_n(
            a.lo,
            b.hi,
        ) * prod_d(x, y),
        (y.n() < 0 && a.lo.n() < 0) ==> mul_n(x, y) * prod_d(a.lo, b.lo) <= mul_n(
            a.lo,
            b.lo,
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
            assert(mul_n(b.hi, a.hi) == mul_n(a.hi, b.hi));
            assert(mul_n(y, a.hi) == mul_n(a.hi, y));
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
            assert(mul_n(b.lo, a.hi) == mul_n(a.hi, b.lo));
            assert(mul_n(y, a.hi) == mul_n(a.hi, y));
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
            assert(mul_n(b.hi, a.lo) == mul_n(a.lo, b.hi));
            assert(mul_n(y, a.lo) == mul_n(a.lo, y));
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
            assert(mul_n(b.lo, a.lo) == mul_n(a.lo, b.lo));
            assert(mul_n(y, a.lo) == mul_n(a.lo, y));
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

/// **The corner rule.** The exact product `x*y`, for `x` in `a`'s range and
/// `y` in `b`'s range, lies between the min and the max of the four exact
/// corner products. This holds for *every* sign pattern, and no case split is
/// visible at this level. [`lemma_mul_corner_lower`] and
/// [`lemma_mul_corner_upper`] each return some corner that brackets `x*y`.
/// [`frac_min`] and [`frac_max`] of all four corners are themselves bounds on
/// every corner (`lemma_frac_min4_le` and `lemma_frac_max4_ge`). The returned
/// corner therefore chains through to the global min and max.
pub proof fn theorem_interval_mul_contains(a: QI, b: QI, x: Rat, y: Rat)
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
        ({
            let (mn, md) = frac_min(
                frac_min(
                    mul_n(a.lo, b.lo),
                    prod_d(a.lo, b.lo),
                    mul_n(a.lo, b.hi),
                    prod_d(a.lo, b.hi),
                ).0,
                frac_min(
                    mul_n(a.lo, b.lo),
                    prod_d(a.lo, b.lo),
                    mul_n(a.lo, b.hi),
                    prod_d(a.lo, b.hi),
                ).1,
                frac_min(
                    mul_n(a.hi, b.lo),
                    prod_d(a.hi, b.lo),
                    mul_n(a.hi, b.hi),
                    prod_d(a.hi, b.hi),
                ).0,
                frac_min(
                    mul_n(a.hi, b.lo),
                    prod_d(a.hi, b.lo),
                    mul_n(a.hi, b.hi),
                    prod_d(a.hi, b.hi),
                ).1,
            );
            mn * prod_d(x, y) <= mul_n(x, y) * md
        }),
        ({
            let (mx, mxd) = frac_max(
                frac_max(
                    mul_n(a.lo, b.lo),
                    prod_d(a.lo, b.lo),
                    mul_n(a.lo, b.hi),
                    prod_d(a.lo, b.hi),
                ).0,
                frac_max(
                    mul_n(a.lo, b.lo),
                    prod_d(a.lo, b.lo),
                    mul_n(a.lo, b.hi),
                    prod_d(a.lo, b.hi),
                ).1,
                frac_max(
                    mul_n(a.hi, b.lo),
                    prod_d(a.hi, b.lo),
                    mul_n(a.hi, b.hi),
                    prod_d(a.hi, b.hi),
                ).0,
                frac_max(
                    mul_n(a.hi, b.lo),
                    prod_d(a.hi, b.lo),
                    mul_n(a.hi, b.hi),
                    prod_d(a.hi, b.hi),
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
