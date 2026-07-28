//! Error-propagation (Lipschitz) lemmas — obligation V7, the enabling
//! layer for the interval type and for composing accumulated bounds.
//!
//! Everything is ghost-level algebra over fractions represented as int
//! pairs with positive denominators, stated division-free. The central
//! predicate is [`frac_close`]: `|a/b - c/d| <= e/f` by cross-multiplication.
//!
//! Proof style (learned the hard way): Z3 diverges on nonlinear identities
//! beyond ~4 variables, so every ring identity is decomposed into explicit
//! vstd distributivity-lemma calls plus tiny (<= 4 variable) AC steps.

use vstd::prelude::*;
#[allow(unused_imports)]
use vstd::arithmetic::mul::*;

#[allow(unused_imports)]
use crate::q::*;
#[allow(unused_imports)]
use crate::specs::*;

verus! {

/// `|an/ad - bn/bd| <= en/ed` (denominators positive), division-free.
pub open spec fn frac_close(an: int, ad: int, bn: int, bd: int, en: int, ed: int) -> bool
    recommends
        ad > 0,
        bd > 0,
        ed > 0,
{
    &&& -(en * (ad * bd)) <= (an * bd - bn * ad) * ed
    &&& (an * bd - bn * ad) * ed <= en * (ad * bd)
}

/// `|an/ad| <= m` (denominator positive), division-free.
pub open spec fn frac_mag_le(an: int, ad: int, m: int) -> bool
    recommends
        ad > 0,
{
    -(m * ad) <= an && an <= m * ad
}

// ---------------------------------------------------------------------------
// Small arithmetic helpers (each a tiny solver query)
// ---------------------------------------------------------------------------

/// Multiply an inequality by a nonnegative factor on the left.
proof fn lemma_mul_le_pos(c: int, x: int, y: int)
    requires
        c >= 0,
        x <= y,
    ensures
        c * x <= c * y,
{
    assert(c * x <= c * y) by (nonlinear_arith)
        requires c >= 0, x <= y;
}

/// Cancel a positive factor from an inequality.
proof fn lemma_cancel_le(a: int, b: int, c: int)
    requires
        a * c <= b * c,
        c > 0,
    ensures
        a <= b,
{
    assert(a <= b) by (nonlinear_arith)
        requires a * c <= b * c, c > 0;
}

/// Two-sided product bound: `|x| <= xb`, `|y| <= yb` give `|x*y| <= xb*yb`.
proof fn lemma_abs_mul_bound(x: int, xb: int, y: int, yb: int)
    requires
        -xb <= x <= xb,
        -yb <= y <= yb,
    ensures
        -(xb * yb) <= x * y <= xb * yb,
{
    assert(-(xb * yb) <= x * y <= xb * yb) by (nonlinear_arith)
        requires -xb <= x <= xb, -yb <= y <= yb;
}

/// A satisfiable closeness bound is nonnegative.
pub proof fn lemma_close_nonneg(an: int, ad: int, bn: int, bd: int, en: int, ed: int)
    requires
        ad > 0,
        bd > 0,
        ed > 0,
        frac_close(an, ad, bn, bd, en, ed),
    ensures
        en >= 0,
{
    assert(en >= 0) by (nonlinear_arith)
        requires
            -(en * (ad * bd)) <= (an * bd - bn * ad) * ed,
            (an * bd - bn * ad) * ed <= en * (ad * bd),
            ad > 0,
            bd > 0;
}

/// `frac_close` is reflexive with any nonnegative bound.
pub proof fn lemma_close_refl(an: int, ad: int, en: int, ed: int)
    requires
        ad > 0,
        ed > 0,
        en >= 0,
    ensures
        frac_close(an, ad, an, ad, en, ed),
{
    assert(en * (ad * ad) >= 0) by (nonlinear_arith)
        requires en >= 0, ad > 0;
}

/// `frac_close` is symmetric.
pub proof fn lemma_close_symm(an: int, ad: int, bn: int, bd: int, en: int, ed: int)
    requires
        frac_close(an, ad, bn, bd, en, ed),
    ensures
        frac_close(bn, bd, an, ad, en, ed),
{
    assert((bn * ad - an * bd) * ed == -((an * bd - bn * ad) * ed)) by (nonlinear_arith);
    assert(en * (bd * ad) == en * (ad * bd)) by (nonlinear_arith);
}

/// Weaken the bound numerator.
pub proof fn lemma_close_weaken(an: int, ad: int, bn: int, bd: int, en: int, en2: int, ed: int)
    requires
        ad > 0,
        bd > 0,
        ed > 0,
        en <= en2,
        frac_close(an, ad, bn, bd, en, ed),
    ensures
        frac_close(an, ad, bn, bd, en2, ed),
{
    assert(en * (ad * bd) <= en2 * (ad * bd)) by (nonlinear_arith)
        requires en <= en2, ad > 0, bd > 0;
}

// ---------------------------------------------------------------------------
// Ring identities, decomposed
// ---------------------------------------------------------------------------

/// `(an*cd - cn*ad) * bd == (an*bd - bn*ad)*cd + (bn*cd - cn*bd)*ad`.
proof fn ring_triangle(an: int, ad: int, bn: int, bd: int, cn: int, cd: int)
    ensures
        (an * cd - cn * ad) * bd == (an * bd - bn * ad) * cd + (bn * cd - cn * bd) * ad,
{
    lemma_mul_is_distributive_sub_other_way(bd, an * cd, cn * ad);
    lemma_mul_is_distributive_sub_other_way(cd, an * bd, bn * ad);
    lemma_mul_is_distributive_sub_other_way(ad, bn * cd, cn * bd);
    assert((an * cd) * bd == (an * bd) * cd) by (nonlinear_arith);
    assert((cn * ad) * bd == (cn * bd) * ad) by (nonlinear_arith);
    assert((bn * ad) * cd == (bn * cd) * ad) by (nonlinear_arith);
}

/// The add split:
/// `(an*bd + bn*ad)*(ad2*bd2) - (an2*bd2 + bn2*ad2)*(ad*bd)
///    == (bd*bd2)*(an*ad2 - an2*ad) + (ad*ad2)*(bn*bd2 - bn2*bd)`.
proof fn ring_add_split(
    an: int, ad: int, an2: int, ad2: int, bn: int, bd: int, bn2: int, bd2: int)
    ensures
        (an * bd + bn * ad) * (ad2 * bd2) - (an2 * bd2 + bn2 * ad2) * (ad * bd)
            == (bd * bd2) * (an * ad2 - an2 * ad) + (ad * ad2) * (bn * bd2 - bn2 * bd),
{
    lemma_mul_is_distributive_add_other_way(ad2 * bd2, an * bd, bn * ad);
    lemma_mul_is_distributive_add_other_way(ad * bd, an2 * bd2, bn2 * ad2);
    lemma_mul_is_distributive_sub(bd * bd2, an * ad2, an2 * ad);
    lemma_mul_is_distributive_sub(ad * ad2, bn * bd2, bn2 * bd);
    assert((an * bd) * (ad2 * bd2) == (bd * bd2) * (an * ad2)) by (nonlinear_arith);
    assert((an2 * bd2) * (ad * bd) == (bd * bd2) * (an2 * ad)) by (nonlinear_arith);
    assert((bn * ad) * (ad2 * bd2) == (ad * ad2) * (bn * bd2)) by (nonlinear_arith);
    assert((bn2 * ad2) * (ad * bd) == (ad * ad2) * (bn2 * bd)) by (nonlinear_arith);
}

/// The mul split:
/// `(an*bn)*(ad2*bd2) - (an2*bn2)*(ad*bd)
///    == (an*ad2)*(bn*bd2 - bn2*bd) + (bn2*bd)*(an*ad2 - an2*ad)`.
proof fn ring_mul_split(
    an: int, ad: int, an2: int, ad2: int, bn: int, bd: int, bn2: int, bd2: int)
    ensures
        (an * bn) * (ad2 * bd2) - (an2 * bn2) * (ad * bd)
            == (an * ad2) * (bn * bd2 - bn2 * bd) + (bn2 * bd) * (an * ad2 - an2 * ad),
{
    lemma_mul_is_distributive_sub(an * ad2, bn * bd2, bn2 * bd);
    lemma_mul_is_distributive_sub(bn2 * bd, an * ad2, an2 * ad);
    assert((an * bn) * (ad2 * bd2) == (an * ad2) * (bn * bd2)) by (nonlinear_arith);
    assert((an2 * bn2) * (ad * bd) == (bn2 * bd) * (an2 * ad)) by (nonlinear_arith);
    assert((an * ad2) * (bn2 * bd) == (bn2 * bd) * (an * ad2)) by (nonlinear_arith);
}

/// Pull a scalar through: `c * (e * x) == e * (c * x)` and `== (e * c) * x`.
proof fn ring_pull_scalar(c: int, e: int, x: int)
    ensures
        c * (e * x) == e * (c * x),
        c * (e * x) == (e * c) * x,
{
    assert(c * (e * x) == e * (c * x)) by (nonlinear_arith);
    assert(c * (e * x) == (e * c) * x) by (nonlinear_arith);
}

/// `(x*y)*z == (x*z)*y` (opaque-argument shuffle).
proof fn ring_shuffle3(x: int, y: int, z: int)
    ensures
        (x * y) * z == (x * z) * y,
{
    assert((x * y) * z == (x * z) * y) by (nonlinear_arith);
}

/// `(a*b)*(c*d) == (a*c)*(b*d)` (opaque-argument 4-swap).
proof fn ring_swap4(a: int, b: int, c: int, d: int)
    ensures
        (a * b) * (c * d) == (a * c) * (b * d),
{
    assert((a * b) * (c * d) == (a * c) * (b * d)) by (nonlinear_arith);
}

/// `c * (-(e*x)) == -(e*(c*x))` (opaque-argument negation pull).
proof fn ring_neg_pull(c: int, e: int, x: int)
    ensures
        c * (-(e * x)) == -(e * (c * x)),
{
    assert(c * (-(e * x)) == -(e * (c * x))) by (nonlinear_arith);
}

// ---------------------------------------------------------------------------
// Triangle inequality
// ---------------------------------------------------------------------------

/// `|a - b| <= e1/ed` and `|b - c| <= e2/ed` give `|a - c| <= (e1+e2)/ed`.
pub proof fn lemma_frac_triangle(
    an: int, ad: int, bn: int, bd: int, cn: int, cd: int, e1: int, e2: int, ed: int)
    requires
        ad > 0,
        bd > 0,
        cd > 0,
        ed > 0,
        frac_close(an, ad, bn, bd, e1, ed),
        frac_close(bn, bd, cn, cd, e2, ed),
    ensures
        frac_close(an, ad, cn, cd, e1 + e2, ed),
{
    let d1 = an * bd - bn * ad;
    let d2 = bn * cd - cn * bd;
    let dt = an * cd - cn * ad;
    ring_triangle(an, ad, bn, bd, cn, cd);
    // (dt*ed)*bd == (d1*ed)*cd + (d2*ed)*ad
    lemma_mul_is_distributive_add_other_way(ed, d1 * cd, d2 * ad);
    ring_shuffle3(dt, bd, ed);
    ring_shuffle3(d1, cd, ed);
    ring_shuffle3(d2, ad, ed);
    assert((dt * ed) * bd == (d1 * ed) * cd + (d2 * ed) * ad);
    // Scale the hypotheses.
    lemma_mul_inequality(d1 * ed, e1 * (ad * bd), cd);
    lemma_mul_inequality(-(e1 * (ad * bd)), d1 * ed, cd);
    lemma_mul_inequality(d2 * ed, e2 * (bd * cd), ad);
    lemma_mul_inequality(-(e2 * (bd * cd)), d2 * ed, ad);
    // Normalize the bound sum to ((e1+e2)*(ad*cd))*bd.
    let x = ad * cd;
    assert((e1 * (ad * bd)) * cd == (e1 * x) * bd) by (nonlinear_arith)
        requires x == ad * cd;
    assert((e2 * (bd * cd)) * ad == (e2 * x) * bd) by (nonlinear_arith)
        requires x == ad * cd;
    lemma_mul_is_distributive_add_other_way(x, e1, e2);
    lemma_mul_is_distributive_add_other_way(bd, e1 * x, e2 * x);
    // Chain and cancel bd on both sides.
    assert((dt * ed) * bd <= ((e1 + e2) * x) * bd);
    lemma_cancel_le(dt * ed, (e1 + e2) * x, bd);
    assert((-(e1 * (ad * bd))) * cd == (-(e1 * x)) * bd) by (nonlinear_arith)
        requires x == ad * cd;
    assert((-(e2 * (bd * cd))) * ad == (-(e2 * x)) * bd) by (nonlinear_arith)
        requires x == ad * cd;
    lemma_mul_is_distributive_add_other_way(bd, -(e1 * x), -(e2 * x));
    assert(-(e1 * x) + -(e2 * x) == -((e1 + e2) * x)) by {
        lemma_mul_is_distributive_add_other_way(x, e1, e2);
    };
    assert((-((e1 + e2) * x)) * bd <= (dt * ed) * bd);
    lemma_cancel_le(-((e1 + e2) * x), dt * ed, bd);
}

// ---------------------------------------------------------------------------
// V7: perturbation bounds for add / sub / mul / recip / div
// ---------------------------------------------------------------------------

/// Addition: perturbing the addends by `e1/ed` and `e2/ed` perturbs the
/// exact sum by at most `(e1+e2)/ed`.
pub proof fn lemma_lip_add(
    an: int, ad: int, an2: int, ad2: int,
    bn: int, bd: int, bn2: int, bd2: int,
    e1: int, e2: int, ed: int)
    requires
        ad > 0, ad2 > 0, bd > 0, bd2 > 0, ed > 0,
        frac_close(an, ad, an2, ad2, e1, ed),
        frac_close(bn, bd, bn2, bd2, e2, ed),
    ensures
        frac_close(
            an * bd + bn * ad, ad * bd,
            an2 * bd2 + bn2 * ad2, ad2 * bd2,
            e1 + e2, ed),
{
    let d1 = an * ad2 - an2 * ad;
    let d2 = bn * bd2 - bn2 * bd;
    let sn = an * bd + bn * ad;
    let sd = ad * bd;
    let tn = an2 * bd2 + bn2 * ad2;
    let td = ad2 * bd2;
    let cb = bd * bd2;
    let ca = ad * ad2;
    ring_add_split(an, ad, an2, ad2, bn, bd, bn2, bd2);
    assert(sn * td - tn * sd == cb * d1 + ca * d2);
    // Multiply through by ed.
    lemma_mul_is_distributive_add_other_way(ed, cb * d1, ca * d2);
    assert((sn * td - tn * sd) * ed == (cb * d1) * ed + (ca * d2) * ed);
    lemma_mul_is_associative(cb, d1, ed);
    lemma_mul_is_associative(ca, d2, ed);
    // Scale the hypotheses by the positive complementary denominators.
    assert(cb > 0) by (nonlinear_arith) requires cb == bd * bd2, bd > 0, bd2 > 0;
    assert(ca > 0) by (nonlinear_arith) requires ca == ad * ad2, ad > 0, ad2 > 0;
    lemma_mul_le_pos(cb, d1 * ed, e1 * ca);
    lemma_mul_le_pos(cb, -(e1 * ca), d1 * ed);
    lemma_mul_le_pos(ca, d2 * ed, e2 * cb);
    lemma_mul_le_pos(ca, -(e2 * cb), d2 * ed);
    // Normalize the bounds to (e1+e2)*(sd*td).
    ring_pull_scalar(cb, e1, ca);
    ring_pull_scalar(ca, e2, cb);
    ring_swap4(bd, bd2, ad, ad2);
    ring_swap4(ad, ad2, bd, bd2);
    assert(cb * ca == (bd * ad) * (bd2 * ad2));
    assert((bd * ad) * (bd2 * ad2) == sd * td) by {
        lemma_mul_is_commutative(bd, ad);
        lemma_mul_is_commutative(bd2, ad2);
    };
    assert(ca * cb == sd * td);
    lemma_mul_is_distributive_add_other_way(sd * td, e1, e2);
    ring_neg_pull(cb, e1, ca);
    ring_neg_pull(ca, e2, cb);
}

/// Subtraction: same bound as addition.
pub proof fn lemma_lip_sub(
    an: int, ad: int, an2: int, ad2: int,
    bn: int, bd: int, bn2: int, bd2: int,
    e1: int, e2: int, ed: int)
    requires
        ad > 0, ad2 > 0, bd > 0, bd2 > 0, ed > 0,
        frac_close(an, ad, an2, ad2, e1, ed),
        frac_close(bn, bd, bn2, bd2, e2, ed),
    ensures
        frac_close(
            an * bd - bn * ad, ad * bd,
            an2 * bd2 - bn2 * ad2, ad2 * bd2,
            e1 + e2, ed),
{
    assert(((-bn) * bd2 - (-bn2) * bd) * ed == -((bn * bd2 - bn2 * bd) * ed)) by (nonlinear_arith);
    assert(frac_close(-bn, bd, -bn2, bd2, e2, ed));
    lemma_lip_add(an, ad, an2, ad2, -bn, bd, -bn2, bd2, e1, e2, ed);
    assert(an * bd + (-bn) * ad == an * bd - bn * ad) by (nonlinear_arith);
    assert(an2 * bd2 + (-bn2) * ad2 == an2 * bd2 - bn2 * ad2) by (nonlinear_arith);
}

/// Multiplication on a bounded domain: if `|a| <= ma` and `|b'| <= mb`,
/// perturbing the factors by `e1/ed`, `e2/ed` perturbs the product by at
/// most `(mb*e1 + ma*e2)/ed`.
pub proof fn lemma_lip_mul(
    an: int, ad: int, an2: int, ad2: int,
    bn: int, bd: int, bn2: int, bd2: int,
    ma: int, mb: int, e1: int, e2: int, ed: int)
    requires
        ad > 0, ad2 > 0, bd > 0, bd2 > 0, ed > 0, ma >= 0, mb >= 0,
        frac_mag_le(an, ad, ma),
        frac_mag_le(bn2, bd2, mb),
        frac_close(an, ad, an2, ad2, e1, ed),
        frac_close(bn, bd, bn2, bd2, e2, ed),
    ensures
        frac_close(an * bn, ad * bd, an2 * bn2, ad2 * bd2, mb * e1 + ma * e2, ed),
{
    let d1 = an * ad2 - an2 * ad;
    let d2 = bn * bd2 - bn2 * bd;
    let pd = ad * bd;
    let qd = ad2 * bd2;
    lemma_close_nonneg(an, ad, an2, ad2, e1, ed);
    lemma_close_nonneg(bn, bd, bn2, bd2, e2, ed);
    ring_mul_split(an, ad, an2, ad2, bn, bd, bn2, bd2);
    let t1 = (an * ad2) * d2;
    let t2 = (bn2 * bd) * d1;
    assert((an * bn) * qd - (an2 * bn2) * pd == t1 + t2);
    lemma_mul_is_distributive_add_other_way(ed, t1, t2);
    assert(((an * bn) * qd - (an2 * bn2) * pd) * ed == t1 * ed + t2 * ed);
    // |an*ad2| <= (ma*ad)*ad2  and  |d2*ed| <= e2*(bd*bd2).
    assert(-((ma * ad) * ad2) <= an * ad2 && an * ad2 <= (ma * ad) * ad2) by (nonlinear_arith)
        requires -(ma * ad) <= an && an <= ma * ad, ad2 > 0;
    lemma_mul_is_associative(an * ad2, d2, ed);
    assert(t1 * ed == (an * ad2) * (d2 * ed));
    lemma_abs_mul_bound(an * ad2, (ma * ad) * ad2, d2 * ed, e2 * (bd * bd2));
    // |bn2*bd| <= (mb*bd2)*bd  and  |d1*ed| <= e1*(ad*ad2).
    assert(-((mb * bd2) * bd) <= bn2 * bd && bn2 * bd <= (mb * bd2) * bd) by (nonlinear_arith)
        requires -(mb * bd2) <= bn2 && bn2 <= mb * bd2, bd > 0;
    lemma_mul_is_associative(bn2 * bd, d1, ed);
    assert(t2 * ed == (bn2 * bd) * (d1 * ed));
    lemma_abs_mul_bound(bn2 * bd, (mb * bd2) * bd, d1 * ed, e1 * (ad * ad2));
    // Normalize the two bound products to (ma*e2)*(pd*qd) and (mb*e1)*(pd*qd).
    let big = pd * qd;
    // ((ma*ad)*ad2)*(e2*(bd*bd2)) == (ma*e2)*((ad*ad2)*(bd*bd2)) == (ma*e2)*big
    lemma_mul_is_associative(ma, ad, ad2);
    ring_swap4(ma, ad * ad2, e2, bd * bd2);
    ring_swap4(ad, ad2, bd, bd2);
    assert(((ma * ad) * ad2) * (e2 * (bd * bd2)) == (ma * e2) * ((ad * bd) * (ad2 * bd2)));
    assert(((ma * ad) * ad2) * (e2 * (bd * bd2)) == (ma * e2) * big);
    // ((mb*bd2)*bd)*(e1*(ad*ad2)) == (mb*e1)*((bd2*bd)*(ad*ad2)) == (mb*e1)*big
    lemma_mul_is_associative(mb, bd2, bd);
    ring_swap4(mb, bd2 * bd, e1, ad * ad2);
    assert((bd2 * bd) * (ad * ad2) == (ad * bd) * (ad2 * bd2)) by (nonlinear_arith);
    assert(((mb * bd2) * bd) * (e1 * (ad * ad2)) == (mb * e1) * big);
    // Combine.
    lemma_mul_is_distributive_add_other_way(big, mb * e1, ma * e2);
}

/// Reciprocal with the argument bounded away from zero: if both values are
/// `>= 1/c` (i.e. `den <= c * num`, `c >= 0`), then perturbing by `e/ed`
/// perturbs the reciprocal by at most `c*c*e/ed`.
pub proof fn lemma_lip_recip(
    bn: int, bd: int, bn2: int, bd2: int, c: int, e: int, ed: int)
    requires
        bd > 0, bd2 > 0, ed > 0, c >= 0,
        bn > 0,
        bn2 > 0,
        bd <= c * bn,
        bd2 <= c * bn2,
        frac_close(bn, bd, bn2, bd2, e, ed),
    ensures
        frac_close(bd, bn, bd2, bn2, (c * c) * e, ed),
{
    lemma_close_nonneg(bn, bd, bn2, bd2, e, ed);
    assert((bd * bn2 - bd2 * bn) * ed == -((bn * bd2 - bn2 * bd) * ed)) by (nonlinear_arith);
    // bd*bd2 <= (c*bn)*(c*bn2) == (c*c)*(bn*bn2)
    assert(bd * bd2 <= (c * bn) * (c * bn2)) by (nonlinear_arith)
        requires bd <= c * bn, bd2 <= c * bn2, bd > 0, bd2 > 0;
    assert((c * bn) * (c * bn2) == (c * c) * (bn * bn2)) by (nonlinear_arith);
    lemma_mul_le_pos(e, bd * bd2, (c * c) * (bn * bn2));
    assert(e * ((c * c) * (bn * bn2)) == ((c * c) * e) * (bn * bn2)) by (nonlinear_arith);
    // Both sides transfer through the negation.
    assert((bd * bn2 - bd2 * bn) * ed <= ((c * c) * e) * (bn * bn2));
    assert(-(((c * c) * e) * (bn * bn2)) <= (bd * bn2 - bd2 * bn) * ed);
}

/// Division with the divisor bounded away from zero, by composition
/// (`a/b == a * (1/b)`): divisors `>= 1/c`, `|a| <= m`, `|1/b'| <= m`
/// give `|a/b - a'/b'| <= m*(e1 + c*c*e2)/ed`.
pub proof fn lemma_lip_div(
    an: int, ad: int, an2: int, ad2: int,
    bn: int, bd: int, bn2: int, bd2: int,
    m: int, c: int, e1: int, e2: int, ed: int)
    requires
        ad > 0, ad2 > 0, bd > 0, bd2 > 0, ed > 0, m >= 0, c >= 0,
        bn > 0,
        bn2 > 0,
        bd <= c * bn,
        bd2 <= c * bn2,
        frac_mag_le(an, ad, m),
        frac_mag_le(bd2, bn2, m),
        frac_close(an, ad, an2, ad2, e1, ed),
        frac_close(bn, bd, bn2, bd2, e2, ed),
    ensures
        frac_close(
            an * bd, ad * bn,
            an2 * bd2, ad2 * bn2,
            m * e1 + m * ((c * c) * e2), ed),
{
    lemma_lip_recip(bn, bd, bn2, bd2, c, e2, ed);
    lemma_lip_mul(an, ad, an2, ad2, bd, bn, bd2, bn2, m, m, e1, (c * c) * e2, ed);
}

} // verus!
