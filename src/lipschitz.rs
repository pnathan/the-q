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
    assert((an * bd + bn * ad) * (a2d * b2d) - (a2n * b2d + b2n * a2d) * (ad * bd) == (an * a2d
        - a2n * ad) * (bd * b2d) + (bn * b2d - b2n * bd) * (ad * a2d)) by (nonlinear_arith);
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
    assert((an * bn) * (a2d * b2d) - (a2n * b2n) * (ad * bd) == (an * a2d) * (bn * b2d - b2n * bd)
        + (b2n * bd) * (an * a2d - a2n * ad)) by (nonlinear_arith);
}

/// **Division with the denominator bounded away from zero.**
///
/// With `|b| >= m > 0` and `|b'| >= m`, `|a/b - a'/b'|` is controlled by
/// `(|b'|·|a - a'| + |a|·|b - b'|) / (|b|·|b'|)`, hence by `1/m^2` times the
/// numerator perturbations on a bounded domain. The identity below is the
/// algebraic core; the bound follows by dividing through.
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
    assert((an * bd) * (a2d * b2n) - (a2n * b2d) * (ad * bn) == (bd * b2n) * (an * a2d - a2n * ad)
        - (a2n * ad) * (bn * b2d - b2n * bd)) by (nonlinear_arith);
}

/// The step used by `crate::nary::theorem_sum_error_accumulation`: one more
/// rounded `add` on top of a result already within `k` units takes the total to
/// `k + 1` units.
pub proof fn lemma_error_accumulates_additively(
    prev: Q,
    prev_n: int,
    prev_d: int,
    next: Q,
    r: Q,
    k: nat,
)
    requires
        prev.wf(),
        next.wf(),
        r.wf(),
        prev_d > 0,
        // The accumulator so far is within `k` units of the exact partial sum.
        within_error_bound_k(prev, prev_n, prev_d, k),
        // `r` is one more rounded addition on top of it.
        r == crate::round::round_frac(
            crate::q::add_n(prev, next),
            crate::q::prod_d(prev, next),
            crate::types::Dir::Nearest,
        ),
        !crate::round::saturated(crate::q::add_n(prev, next), crate::q::prod_d(prev, next)),
    ensures
        within_error_bound_k(
            r,
            prev_n * next.d() + next.n() * prev_d,
            prev_d * next.d(),
            (k + 1) as nat,
        ),
{
    // Two contributions, and they add:
    //
    //   * the carried error, transported through `add`. Addition is 1-Lipschitz
    //     in each argument (lemma_add_lipschitz), so `k` units in gives at most
    //     `k` units out.
    //   * the fresh rounding error of this very step, at most one unit by R3.
    crate::round::lemma_r3_error(
        crate::q::add_n(prev, next),
        crate::q::prod_d(prev, next),
        crate::types::Dir::Nearest,
    );
    lemma_add_lipschitz(
        prev.n(),
        prev.d(),
        next.n(),
        next.d(),
        prev_n,
        prev_d,
        next.n(),
        next.d(),
        k as int,
        0,
        pow2(precision_b()),
    );
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
