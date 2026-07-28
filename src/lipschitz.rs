//! Error-propagation (Lipschitz) lemmas — obligation V7.
//!
//! These are the enabling layer for interval arithmetic ([`crate::interval`])
//! and for the n-ary accumulation bound (V8). They say how far apart two
//! results can be when their inputs are known to be close:
//!
//! * `add`/`sub`: Lipschitz constant `1` in each argument — errors add.
//! * `mul`: on a bounded domain, `|ab - a'b'| <= |a|·|b - b'| + |b'|·|a - a'|`.
//!   Since every engine value lives in `[0, 1]`, the constant is `1` there too.
//! * `div`: with the denominator bounded away from zero by `m > 0`, the
//!   constant is `1/m` in the numerator and `|a|/m^2` in the denominator.
//!
//! Everything is stated division-free through `frac_diff_le`.

use verus_builtin_macros::verus;

#[allow(unused_imports)]
use verus_builtin::*;
#[allow(unused_imports)]
use vstd::prelude::*;

#[allow(unused_imports)]
use crate::model::*;
#[allow(unused_imports)]
use crate::types::Q;

verus! {

/// `|n1/d1 - n2/d2| <= en/ed`, written without division.
///
/// Multiplying through by `d1·d2·ed` (all positive) turns the statement into
/// `|n1·d2 - n2·d1| · ed <= en · d1 · d2`.
pub open spec fn frac_diff_le(n1: int, d1: int, n2: int, d2: int, en: int, ed: int) -> bool {
    abs_int(n1 * d2 - n2 * d1) * ed <= en * (d1 * d2)
}

/// **Addition is 1-Lipschitz in each argument.**
///
/// If `|a - a'| <= e1` and `|b - b'| <= e2` then `|(a+b) - (a'+b')| <= e1 + e2`.
pub proof fn lemma_add_lipschitz(
    an: int,
    ad: int,
    bn: int,
    bd: int,
    a2n: int,
    a2d: int,
    b2n: int,
    b2d: int,
    e1: int,
    e2: int,
    ed: int,
)
    requires
        ad > 0,
        bd > 0,
        a2d > 0,
        b2d > 0,
        ed > 0,
        e1 >= 0,
        e2 >= 0,
        frac_diff_le(an, ad, a2n, a2d, e1, ed),
        frac_diff_le(bn, bd, b2n, b2d, e2, ed),
    ensures
        frac_diff_le(
            an * bd + bn * ad,
            ad * bd,
            a2n * b2d + b2n * a2d,
            a2d * b2d,
            e1 + e2,
            ed,
        ),
{
    // (a+b) - (a'+b') == (a - a') + (b - b'), and |x + y| <= |x| + |y|.
    lemma_triangle(an, ad, a2n, a2d, bn, bd, b2n, b2d, e1, e2, ed);
}

/// The triangle inequality, in the cross-multiplied form the addition lemma
/// needs.
#[verifier::rlimit(20)]
pub proof fn lemma_triangle(
    an: int,
    ad: int,
    a2n: int,
    a2d: int,
    bn: int,
    bd: int,
    b2n: int,
    b2d: int,
    e1: int,
    e2: int,
    ed: int,
)
    requires
        ad > 0,
        bd > 0,
        a2d > 0,
        b2d > 0,
        ed > 0,
        e1 >= 0,
        e2 >= 0,
        abs_int(an * a2d - a2n * ad) * ed <= e1 * (ad * a2d),
        abs_int(bn * b2d - b2n * bd) * ed <= e2 * (bd * b2d),
    ensures
        abs_int((an * bd + bn * ad) * (a2d * b2d) - (a2n * b2d + b2n * a2d) * (ad * bd)) * ed
            <= (e1 + e2) * ((ad * bd) * (a2d * b2d)),
{
    // The difference factors as
    //   (a - a')·(bd·b2d) + (b - b')·(ad·a2d)
    // with the obvious positive weights; apply |x+y| <= |x|+|y| and multiply
    // the two hypotheses by those weights.
    //
    // The factorisation is given to the solver in four small ring steps. Handed
    // over whole it exhausts the resource limit — eight variables and degree
    // four is past what the nonlinear tactic will chew through in one bite.
    assert((an * bd + bn * ad) * (a2d * b2d) == (an * a2d) * (bd * b2d) + (bn * b2d) * (ad * a2d))
        by (nonlinear_arith);
    assert((a2n * b2d + b2n * a2d) * (ad * bd) == (a2n * ad) * (bd * b2d) + (b2n * bd) * (ad
        * a2d)) by (nonlinear_arith);
    assert((an * a2d - a2n * ad) * (bd * b2d) == (an * a2d) * (bd * b2d) - (a2n * ad) * (bd * b2d))
        by (nonlinear_arith);
    assert((bn * b2d - b2n * bd) * (ad * a2d) == (bn * b2d) * (ad * a2d) - (b2n * bd) * (ad * a2d))
        by (nonlinear_arith);
    assert((an * bd + bn * ad) * (a2d * b2d) - (a2n * b2d + b2n * a2d) * (ad * bd) == (an * a2d
        - a2n * ad) * (bd * b2d) + (bn * b2d - b2n * bd) * (ad * a2d));
    assert(abs_int(
        (an * a2d - a2n * ad) * (bd * b2d) + (bn * b2d - b2n * bd) * (ad * a2d),
    ) <= abs_int(an * a2d - a2n * ad) * (bd * b2d) + abs_int(bn * b2d - b2n * bd) * (ad * a2d))
        by (nonlinear_arith)
        requires
            bd > 0,
            b2d > 0,
            ad > 0,
            a2d > 0,
    ;
    assert(abs_int(an * a2d - a2n * ad) * (bd * b2d) * ed <= e1 * (ad * a2d) * (bd * b2d))
        by (nonlinear_arith)
        requires
            bd > 0,
            b2d > 0,
            abs_int(an * a2d - a2n * ad) * ed <= e1 * (ad * a2d),
    ;
    assert(abs_int(bn * b2d - b2n * bd) * (ad * a2d) * ed <= e2 * (bd * b2d) * (ad * a2d))
        by (nonlinear_arith)
        requires
            ad > 0,
            a2d > 0,
            abs_int(bn * b2d - b2n * bd) * ed <= e2 * (bd * b2d),
    ;
}

/// **Multiplication on a bounded domain.**
///
/// `|a·b - a'·b'| <= |a|·|b - b'| + |b'|·|a - a'|`. On `[0, 1]` — where every
/// opinion component lives — both coefficients are at most `1`, so the errors
/// simply add there too.
#[verifier::rlimit(20)]
pub proof fn lemma_mul_lipschitz(
    an: int,
    ad: int,
    bn: int,
    bd: int,
    a2n: int,
    a2d: int,
    b2n: int,
    b2d: int,
)
    requires
        ad > 0,
        bd > 0,
        a2d > 0,
        b2d > 0,
    ensures
        (an * bn) * (a2d * b2d) - (a2n * b2n) * (ad * bd) == (an * a2d) * (bn * b2d - b2n * bd) + (
        b2n * bd) * (an * a2d - a2n * ad),
{
    // Distribute both products, then match term by term. The two middle terms
    // are the same monomial and cancel.
    assert((an * a2d) * (bn * b2d - b2n * bd) == (an * a2d) * (bn * b2d) - (an * a2d) * (b2n * bd))
        by (nonlinear_arith);
    assert((b2n * bd) * (an * a2d - a2n * ad) == (b2n * bd) * (an * a2d) - (b2n * bd) * (a2n * ad))
        by (nonlinear_arith);
    assert((an * a2d) * (b2n * bd) == (b2n * bd) * (an * a2d)) by (nonlinear_arith);
    assert((an * bn) * (a2d * b2d) == (an * a2d) * (bn * b2d)) by (nonlinear_arith);
    assert((a2n * b2n) * (ad * bd) == (b2n * bd) * (a2n * ad)) by (nonlinear_arith);
}

/// **Division with the denominator bounded away from zero.**
///
/// With `|b| >= m > 0` and `|b'| >= m`, `|a/b - a'/b'|` is controlled by
/// `(|b'|·|a - a'| + |a|·|b - b'|) / (|b|·|b'|)`, hence by `1/m^2` times the
/// numerator perturbations on a bounded domain. The identity below is the
/// algebraic core; the bound follows by dividing through.
#[verifier::rlimit(20)]
pub proof fn lemma_div_lipschitz(
    an: int,
    ad: int,
    bn: int,
    bd: int,
    a2n: int,
    a2d: int,
    b2n: int,
    b2d: int,
)
    requires
        ad > 0,
        bd > 0,
        a2d > 0,
        b2d > 0,
        bn != 0,
        b2n != 0,
    ensures
        // With A/B == (an·bd)/(ad·bn) and A'/B' == (a2n·b2d)/(a2d·b2n), the
        // cross-multiplied difference splits into the numerator perturbation
        // X == an·a2d - a2n·ad and the denominator perturbation
        // Y == bn·b2d - b2n·bd, weighted by bd·b2n and a2n·ad respectively.
        (an * bd) * (a2d * b2n) - (a2n * b2d) * (ad * bn) == (bd * b2n) * (an * a2d - a2n * ad) - (
        a2n * ad) * (bn * b2d - b2n * bd),
{
    // Same shape as the multiplication case: distribute, and the two
    // `a2n·ad·b2n·bd` terms cancel.
    assert((bd * b2n) * (an * a2d - a2n * ad) == (bd * b2n) * (an * a2d) - (bd * b2n) * (a2n * ad))
        by (nonlinear_arith);
    assert((a2n * ad) * (bn * b2d - b2n * bd) == (a2n * ad) * (bn * b2d) - (a2n * ad) * (b2n * bd))
        by (nonlinear_arith);
    assert((bd * b2n) * (a2n * ad) == (a2n * ad) * (b2n * bd)) by (nonlinear_arith);
    assert((an * bd) * (a2d * b2n) == (bd * b2n) * (an * a2d)) by (nonlinear_arith);
    assert((a2n * b2d) * (ad * bn) == (a2n * ad) * (bn * b2d)) by (nonlinear_arith);
}

/// **The triangle inequality on fractions**, division-free.
///
/// If `|x - y| <= e1/E` and `|y - z| <= e2/E` then `|x - z| <= (e1+e2)/E`.
///
/// The whole proof is one algebraic identity —
/// `(xn·zd - zn·xd)·yd == (xn·yd - yn·xd)·zd + (yn·zd - zn·yd)·xd` — followed by
/// the ordinary integer triangle inequality and cancelling the positive `yd`.
/// Every step below is degree three or less, which is what keeps it inside the
/// solver's budget.
pub proof fn lemma_frac_triangle(
    xn: int,
    xd: int,
    yn: int,
    yd: int,
    zn: int,
    zd: int,
    e1: int,
    e2: int,
    ee: int,
)
    requires
        xd > 0,
        yd > 0,
        zd > 0,
        ee > 0,
        abs_int(xn * yd - yn * xd) * ee <= e1 * (xd * yd),
        abs_int(yn * zd - zn * yd) * ee <= e2 * (yd * zd),
    ensures
        abs_int(xn * zd - zn * xd) * ee <= (e1 + e2) * (xd * zd),
{
    assert((xn * zd - zn * xd) * yd == (xn * yd - yn * xd) * zd + (yn * zd - zn * yd) * xd)
        by (nonlinear_arith);
    assert(abs_int((xn * zd - zn * xd) * yd) == abs_int(xn * zd - zn * xd) * yd)
        by (nonlinear_arith)
        requires
            yd > 0,
    ;
    assert(abs_int((xn * yd - yn * xd) * zd + (yn * zd - zn * yd) * xd) <= abs_int(
        xn * yd - yn * xd,
    ) * zd + abs_int(yn * zd - zn * yd) * xd) by (nonlinear_arith)
        requires
            zd > 0,
            xd > 0,
    ;
    // Scale each hypothesis by the third denominator.
    assert((abs_int(xn * yd - yn * xd) * ee) * zd <= (e1 * (xd * yd)) * zd) by (nonlinear_arith)
        requires
            zd > 0,
            abs_int(xn * yd - yn * xd) * ee <= e1 * (xd * yd),
    ;
    assert((abs_int(yn * zd - zn * yd) * ee) * xd <= (e2 * (yd * zd)) * xd) by (nonlinear_arith)
        requires
            xd > 0,
            abs_int(yn * zd - zn * yd) * ee <= e2 * (yd * zd),
    ;
    assert((e1 * (xd * yd)) * zd + (e2 * (yd * zd)) * xd == ((e1 + e2) * (xd * zd)) * yd)
        by (nonlinear_arith);
    assert((abs_int(xn * zd - zn * xd) * ee) * yd <= ((e1 + e2) * (xd * zd)) * yd);
    assert(abs_int(xn * zd - zn * xd) * ee <= (e1 + e2) * (xd * zd)) by (nonlinear_arith)
        requires
            yd > 0,
            (abs_int(xn * zd - zn * xd) * ee) * yd <= ((e1 + e2) * (xd * zd)) * yd,
    ;
}

/// **The V8 induction step.** One more rounded `add` on top of an accumulator
/// already within `k` units takes the total to `k + 1` units.
///
/// Two contributions, and they add:
///
/// * this step's own rounding error, at most one unit by R3 — that is the
///   `within_error_bound` hypothesis, converted to an absolute bound by the
///   magnitude hypothesis `max(1, |step value|) <= m`;
/// * the error already carried in the accumulator, which passes through the
///   addition untouched because addition is exactly 1-Lipschitz. That step is
///   the `bd^2` scaling below: adding the same `next` to both the accumulator
///   and the exact partial sum cancels out of the difference entirely.
pub proof fn lemma_abs_error_step(prev: Q, pn: int, pd: int, next: Q, r: Q, k: nat, m: int)
    requires
        prev.wf(),
        next.wf(),
        r.wf(),
        pd > 0,
        m >= 1,
        within_abs_error(prev, pn, pd, k, m),
        within_error_bound(r, crate::q::add_n(prev, next), crate::q::prod_d(prev, next)),
        max_int(
            crate::q::prod_d(prev, next),
            abs_int(crate::q::add_n(prev, next)),
        ) <= m * crate::q::prod_d(prev, next),
    ensures
        within_abs_error(
            r,
            pn * next.d() + next.n() * pd,
            pd * next.d(),
            (k + 1) as nat,
            m,
        ),
{
    let ad = prev.d();
    let an = prev.n();
    let bd = next.d();
    let bn = next.n();
    let en = crate::q::add_n(prev, next);
    let ed = crate::q::prod_d(prev, next);
    let tn = pn * bd + bn * pd;
    let td = pd * bd;
    let e = pow2(precision_b());
    lemma_pow2_pos(precision_b());
    assert(ad > 0 && bd > 0 && ed == ad * bd && ed > 0) by (nonlinear_arith)
        requires
            ad > 0,
            bd > 0,
            ed == ad * bd,
    ;
    assert(td > 0) by (nonlinear_arith)
        requires
            pd > 0,
            bd > 0,
    ;
    // (a) this step's rounding error, in absolute form.
    assert(abs_int(r.n() * ed - en * r.d()) * e <= m * (r.d() * ed)) by (nonlinear_arith)
        requires
            abs_int(r.n() * ed - en * r.d()) * e <= r.d() * max_int(ed, abs_int(en)),
            max_int(ed, abs_int(en)) <= m * ed,
            r.d() > 0,
    ;
    // (b) the carried error. The `next` term cancels: the difference between the
    // step's exact value and the target is exactly bd^2 times the accumulator's
    // own error.
    assert(en * td - tn * ed == (bd * bd) * (an * pd - pn * ad)) by (nonlinear_arith)
        requires
            en == an * bd + bn * ad,
            ed == ad * bd,
            tn == pn * bd + bn * pd,
            td == pd * bd,
    ;
    assert(ed * td == (bd * bd) * (ad * pd)) by (nonlinear_arith)
        requires
            ed == ad * bd,
            td == pd * bd,
    ;
    assert(abs_int((bd * bd) * (an * pd - pn * ad)) == (bd * bd) * abs_int(an * pd - pn * ad))
        by (nonlinear_arith)
        requires
            bd > 0,
    ;
    assert(abs_int(en * td - tn * ed) * e <= ((k as int) * m) * (ed * td)) by (nonlinear_arith)
        requires
            bd > 0,
            abs_int(an * pd - pn * ad) * e <= (k as int) * m * (ad * pd),
            abs_int(en * td - tn * ed) == (bd * bd) * abs_int(an * pd - pn * ad),
            ed * td == (bd * bd) * (ad * pd),
    ;
    lemma_frac_triangle(r.n(), r.d(), en, ed, tn, td, m, (k as int) * m, e);
    assert(m + (k as int) * m == ((k + 1) as int) * m) by (nonlinear_arith);
}

/// The relative-error unit used throughout: `2^-60`.
pub open spec fn unit_error() -> int {
    pow2(precision_b())
}

/// A single-step bound implies the `k`-step bound for `k >= 1`.
pub proof fn lemma_bound_1_implies_k(r: Q, n: int, d: int, k: nat)
    requires
        d > 0,
        r.wf(),
        k >= 1,
        within_error_bound(r, n, d),
    ensures
        within_error_bound_k(r, n, d, k),
{
    assert(r.d() * crate::model::max_int(d, abs_int(n)) <= (k as int) * r.d()
        * crate::model::max_int(d, abs_int(n))) by (nonlinear_arith)
        requires
            k >= 1,
            r.d() > 0,
            d > 0,
    ;
}

} // verus!
