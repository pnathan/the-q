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
//!
//! `mul` and `div` each appear twice: once as a bare algebraic identity
//! (`lemma_mul_lipschitz`, `lemma_div_lipschitz`) and once as the bound that
//! identity was always meant to support (`lemma_mul_lipschitz_bound`,
//! `lemma_div_lipschitz_bound`). The identities came first and callers depend on
//! them, so they are kept as-is; the bounds are the form you want when composing
//! two `frac_diff_le` hypotheses through a product or a quotient, which the
//! identity alone will not do for you.
//!
//! The quotient bound is *not* built on the quotient identity. Division is
//! multiplication by the reciprocal, so it is `lemma_recip_lipschitz_bound` fed
//! into `lemma_mul_lipschitz_bound` — shorter to state and far cheaper for the
//! solver than the four-way cross-multiplied difference taken head-on.

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

/// `|u + v| <= |u| + |v|` and `|u - v| <= |u| + |v|`.
///
/// Both directions in one lemma because the product bound needs the first and
/// the quotient bound needs the second. Purely a case split on two signs, so it
/// costs nothing; it exists so call sites can name the step instead of hoping
/// the solver takes it.
pub proof fn lemma_abs_triangle(u: int, v: int)
    ensures
        abs_int(u + v) <= abs_int(u) + abs_int(v),
        abs_int(u - v) <= abs_int(u) + abs_int(v),
{
}

/// `|u · v| == |u| · |v|`, both signs unknown.
///
/// [`crate::model::lemma_abs_mul_pos`] covers the case where one factor is
/// known positive, which is most of them. This is the general one, needed when a
/// numerator of unknown sign multiplies a difference of unknown sign — exactly
/// what the product and quotient bounds run into.
pub proof fn lemma_abs_prod(u: int, v: int)
    ensures
        abs_int(u * v) == abs_int(u) * abs_int(v),
{
    if v > 0 {
        lemma_abs_mul_pos(u, v);
        assert(abs_int(v) == v);
    } else if v == 0 {
        assert(u * v == 0) by (nonlinear_arith)
            requires
                v == 0,
        ;
        assert(abs_int(u) * 0 == 0) by (nonlinear_arith);
    } else {
        // Fold the sign of `v` out and reuse the positive case. Every rewrite
        // is spelled out: the solver has to be walked from `|u·(-v)|` to
        // `|u·v|` a step at a time, because each bridge is an equality *under*
        // an `abs_int` rather than a bare arithmetic step.
        lemma_abs_mul_pos(u, -v);
        assert(abs_int(u * (-v)) == abs_int(u) * (-v));
        assert(u * (-v) == -(u * v)) by (nonlinear_arith);
        assert(abs_int(u * (-v)) == abs_int(-(u * v)));
        assert(abs_int(-(u * v)) == abs_int(u * v));
        assert(abs_int(v) == -v);
        assert(abs_int(u) * (-v) == abs_int(u) * abs_int(v));
    }
}

/// Scaling a `frac_diff_le` by a positive constant: `en/ed == (en·c)/(ed·c)`.
///
/// Needed whenever two bounds carried over different error denominators have to
/// be brought onto a common one before they can be combined.
pub proof fn lemma_frac_diff_scale(
    n1: int,
    d1: int,
    n2: int,
    d2: int,
    en: int,
    ed: int,
    c: int,
)
    requires
        c > 0,
        frac_diff_le(n1, d1, n2, d2, en, ed),
    ensures
        frac_diff_le(n1, d1, n2, d2, en * c, ed * c),
{
    let a = abs_int(n1 * d2 - n2 * d1);
    lemma_mul_le_mono(c, a * ed, en * (d1 * d2));
    assert(c * (a * ed) == a * (ed * c)) by (nonlinear_arith);
    assert(c * (en * (d1 * d2)) == (en * c) * (d1 * d2)) by (nonlinear_arith);
}

/// Multiplication by a non-negative constant preserves `<=`.
///
/// A one-line fact, but the bounds below apply it a dozen times with the
/// multiplier being a different five-factor product each time. Naming it keeps
/// each of those a rewrite rather than another nonlinear goal.
pub proof fn lemma_mul_le_mono(u: int, v: int, w: int)
    requires
        u >= 0,
        v <= w,
    ensures
        u * v <= u * w,
{
    assert(u * v <= u * w) by (nonlinear_arith)
        requires
            u >= 0,
            v <= w,
    ;
}

/// Two `<=` between non-negatives multiply.
pub proof fn lemma_mul_le_mono2(a: int, b: int, c: int, d: int)
    requires
        0 <= a <= c,
        0 <= b <= d,
    ensures
        a * b <= c * d,
{
    lemma_mul_le_mono(a, b, d);
    lemma_mul_le_mono(d, a, c);
    assert(a * d == d * a) by (nonlinear_arith);
    assert(d * c == c * d) by (nonlinear_arith);
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
    assert((an * bd + bn * ad) * (a2d * b2d) == (an * bd) * (a2d * b2d) + (bn * ad) * (a2d * b2d))
        by (nonlinear_arith);
    assert((an * bd) * (a2d * b2d) == (an * a2d) * (bd * b2d)) by (nonlinear_arith);
    assert((bn * ad) * (a2d * b2d) == (bn * b2d) * (ad * a2d)) by (nonlinear_arith);
    assert((a2n * b2d + b2n * a2d) * (ad * bd) == (a2n * b2d) * (ad * bd) + (b2n * a2d) * (ad
        * bd)) by (nonlinear_arith);
    assert((a2n * b2d) * (ad * bd) == (a2n * ad) * (bd * b2d)) by (nonlinear_arith);
    assert((b2n * a2d) * (ad * bd) == (b2n * bd) * (ad * a2d)) by (nonlinear_arith);
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
    // Assemble: scale the triangle inequality by `ed`, then chain the two
    // weighted hypotheses. Each step names its operands so the blocks stay
    // small enough to discharge.
    let dd = (an * bd + bn * ad) * (a2d * b2d) - (a2n * b2d + b2n * a2d) * (ad * bd);
    let t = abs_int(an * a2d - a2n * ad) * (bd * b2d) + abs_int(bn * b2d - b2n * bd) * (ad * a2d);
    assert(abs_int(dd) <= t);
    assert(abs_int(dd) * ed <= t * ed) by (nonlinear_arith)
        requires
            ed > 0,
            abs_int(dd) <= t,
    ;
    assert(t * ed == abs_int(an * a2d - a2n * ad) * (bd * b2d) * ed + abs_int(
        bn * b2d - b2n * bd,
    ) * (ad * a2d) * ed) by (nonlinear_arith)
        requires
            t == abs_int(an * a2d - a2n * ad) * (bd * b2d) + abs_int(bn * b2d - b2n * bd) * (ad
                * a2d),
    ;
    assert(e1 * (ad * a2d) * (bd * b2d) + e2 * (bd * b2d) * (ad * a2d) == (e1 + e2) * ((ad * bd) * (
    a2d * b2d))) by (nonlinear_arith);
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

/// **The product bound**: two `frac_diff_le` hypotheses compose through a
/// multiplication.
///
/// Given `|a - a'| <= e1/ed`, `|b - b'| <= e2/ed`, `|a| <= ca` and `|b'| <= cb`,
/// this concludes `|a·b - a'·b'| <= (ca·e2 + cb·e1)/ed`. The two magnitude
/// bounds are stated division-free as `|an| <= ca·ad` and `|b2n| <= cb·b2d`.
///
/// Note which side each magnitude bound is on: it is `|a|` (the *first*
/// argument, unprimed) and `|b'|` (the *second* argument, primed). That is what
/// [`lemma_mul_lipschitz`]'s identity hands you, and picking the other diagonal
/// would need a different identity.
///
/// On `[0, 1]` both constants are `1`, which is [`lemma_mul_lipschitz_unit`] —
/// the case the module header is talking about when it says errors simply add.
#[verifier::rlimit(40)]
pub proof fn lemma_mul_lipschitz_bound(
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
    ca: int,
    cb: int,
)
    requires
        ad > 0,
        bd > 0,
        a2d > 0,
        b2d > 0,
        ed > 0,
        e1 >= 0,
        e2 >= 0,
        ca >= 0,
        cb >= 0,
        abs_int(an) <= ca * ad,
        abs_int(b2n) <= cb * b2d,
        frac_diff_le(an, ad, a2n, a2d, e1, ed),
        frac_diff_le(bn, bd, b2n, b2d, e2, ed),
    ensures
        frac_diff_le(an * bn, ad * bd, a2n * b2n, a2d * b2d, ca * e2 + cb * e1, ed),
{
    // Every absolute value is bound to a name before it reaches a nonlinear
    // goal. `abs_int` is an open spec fn, so left inline it unfolds to an
    // if-then-else inside the polynomial and the arithmetic solver ends up
    // case-splitting under every product — which is how the first version of
    // this proof spent 25 minutes and then exceeded its rlimit. Named, each one
    // is an opaque atom and the goals below are plain ring identities.
    let x = an * a2d - a2n * ad;
    let y = bn * b2d - b2n * bd;
    let p = (an * bn) * (a2d * b2d) - (a2n * b2n) * (ad * bd);
    let ax = abs_int(x);
    let ay = abs_int(y);
    let ap = abs_int(p);
    let pa = abs_int(an);
    let pb = abs_int(b2n);

    // Step 1: the identity, unchanged.
    lemma_mul_lipschitz(an, ad, bn, bd, a2n, a2d, b2n, b2d);
    assert(p == (an * a2d) * y + (b2n * bd) * x);

    // Step 2: |p| <= (pa·ay)·a2d + (pb·ax)·bd. Each product is re-associated so
    // the positive denominator is the outer factor, which is the shape
    // `lemma_abs_mul_pos` wants; the remaining unknown-sign pair goes through
    // `lemma_abs_prod`.
    lemma_abs_triangle((an * a2d) * y, (b2n * bd) * x);
    assert((an * a2d) * y == (an * y) * a2d) by (nonlinear_arith);
    assert((b2n * bd) * x == (b2n * x) * bd) by (nonlinear_arith);
    lemma_abs_mul_pos(an * y, a2d);
    lemma_abs_mul_pos(b2n * x, bd);
    lemma_abs_prod(an, y);
    lemma_abs_prod(b2n, x);
    assert(ap <= (pa * ay) * a2d + (pb * ax) * bd);

    // Step 3: scale by `ed` and regroup so each hypothesis appears verbatim as
    // a factor — `ay·ed` and `ax·ed` are exactly the two `frac_diff_le`s. The
    // regrouping is split into three small identities rather than one wide one.
    lemma_mul_le_mono(ed, ap, (pa * ay) * a2d + (pb * ax) * bd);
    assert(ap * ed == ed * ap) by (nonlinear_arith);
    assert(ed * ((pa * ay) * a2d + (pb * ax) * bd) == ed * ((pa * ay) * a2d) + ed * ((pb * ax) * bd))
        by (nonlinear_arith);
    assert(ed * ((pa * ay) * a2d) == (pa * a2d) * (ay * ed)) by (nonlinear_arith);
    assert(ed * ((pb * ax) * bd) == (pb * bd) * (ax * ed)) by (nonlinear_arith);

    // Step 4: discharge the two hypotheses.
    assert(pa * a2d >= 0) by (nonlinear_arith)
        requires
            pa >= 0,
            a2d > 0,
    ;
    assert(pb * bd >= 0) by (nonlinear_arith)
        requires
            pb >= 0,
            bd > 0,
    ;
    lemma_mul_le_mono(pa * a2d, ay * ed, e2 * (bd * b2d));
    lemma_mul_le_mono(pb * bd, ax * ed, e1 * (ad * a2d));

    // Step 5: replace the two magnitudes by their ceilings. The multiplier in
    // each case is everything except the magnitude itself, which is why it is
    // written in that odd order. These are spelled out in full rather than
    // named: a `let` binding is invisible inside `by (nonlinear_arith)`, whose
    // context holds only its own `requires`, so a goal like `m1 >= 0` over a
    // named product is simply unprovable there.
    assert(a2d * (e2 * (bd * b2d)) >= 0) by (nonlinear_arith)
        requires
            a2d > 0,
            e2 >= 0,
            bd > 0,
            b2d > 0,
    ;
    assert(bd * (e1 * (ad * a2d)) >= 0) by (nonlinear_arith)
        requires
            bd > 0,
            e1 >= 0,
            ad > 0,
            a2d > 0,
    ;
    lemma_mul_le_mono(a2d * (e2 * (bd * b2d)), pa, ca * ad);
    lemma_mul_le_mono(bd * (e1 * (ad * a2d)), pb, cb * b2d);
    assert((a2d * (e2 * (bd * b2d))) * pa == (pa * a2d) * (e2 * (bd * b2d))) by (nonlinear_arith);
    assert((bd * (e1 * (ad * a2d))) * pb == (pb * bd) * (e1 * (ad * a2d))) by (nonlinear_arith);
    assert((a2d * (e2 * (bd * b2d))) * (ca * ad) == (ca * e2) * ((ad * bd) * (a2d * b2d)))
        by (nonlinear_arith);
    assert((bd * (e1 * (ad * a2d))) * (cb * b2d) == (cb * e1) * ((ad * bd) * (a2d * b2d)))
        by (nonlinear_arith);

    // Step 6: add the two halves.
    assert((ca * e2) * ((ad * bd) * (a2d * b2d)) + (cb * e1) * ((ad * bd) * (a2d * b2d)) == (ca * e2
        + cb * e1) * ((ad * bd) * (a2d * b2d))) by (nonlinear_arith);
}

/// The product bound on the unit domain: with `|a| <= 1` and `|b'| <= 1` the
/// errors simply add.
///
/// This is the case every opinion component in the fusion engine is in, and it
/// is the claim the module header makes. Stating it separately means callers on
/// `[0, 1]` never have to pass a pair of magnitude constants that are always
/// both `1`.
pub proof fn lemma_mul_lipschitz_unit(
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
        abs_int(an) <= ad,
        abs_int(b2n) <= b2d,
        frac_diff_le(an, ad, a2n, a2d, e1, ed),
        frac_diff_le(bn, bd, b2n, b2d, e2, ed),
    ensures
        frac_diff_le(an * bn, ad * bd, a2n * b2n, a2d * b2d, e1 + e2, ed),
{
    assert(1 * ad == ad);
    assert(1 * b2d == b2d);
    lemma_mul_lipschitz_bound(an, ad, bn, bd, a2n, a2d, b2n, b2d, e1, e2, ed, 1, 1);
    assert(1 * e2 + 1 * e1 == e1 + e2);
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

/// **The reciprocal bound.** If `b` and `b'` are both at least `m == mn/md > 0`
/// and `|b - b'| <= e2/ed`, then `|1/b - 1/b'| <= (e2·md^2)/(ed·mn^2)`.
///
/// This is where the quadratic cost of perturbing a divisor actually lives:
/// `1/b - 1/b' == (b' - b)/(b·b')`, so the numerator perturbation passes through
/// unchanged and the denominator contributes `1/m` twice.
///
/// The lower bound is supplied division-free as `mn·bd <= md·bn`, which is
/// `b >= mn/md` cross-multiplied. Callers with `b >= 1/2` pass `mn = 1, md = 2`.
pub proof fn lemma_recip_lipschitz_bound(
    bn: int,
    bd: int,
    b2n: int,
    b2d: int,
    e2: int,
    ed: int,
    mn: int,
    md: int,
)
    requires
        bd > 0,
        b2d > 0,
        ed > 0,
        bn > 0,
        b2n > 0,
        mn > 0,
        md > 0,
        e2 >= 0,
        mn * bd <= md * bn,
        mn * b2d <= md * b2n,
        frac_diff_le(bn, bd, b2n, b2d, e2, ed),
    ensures
        frac_diff_le(bd, bn, b2d, b2n, e2 * (md * md), ed * (mn * mn)),
{
    let y = bn * b2d - b2n * bd;
    let ay = abs_int(y);

    // Flipping both fractions negates the cross-difference, which `abs_int`
    // does not see.
    assert(bd * b2n - b2d * bn == -y) by (nonlinear_arith)
        requires
            y == bn * b2d - b2n * bd,
    ;
    assert(abs_int(-y) == ay);

    // Scale the hypothesis `ay·ed <= e2·(bd·b2d)` by `mn^2`, and park the two
    // factors of `mn` next to the two denominators they are about to displace.
    assert(mn * mn >= 0) by (nonlinear_arith)
        requires
            mn > 0,
    ;
    lemma_mul_le_mono(mn * mn, ay * ed, e2 * (bd * b2d));
    assert((mn * mn) * (ay * ed) == ay * (ed * (mn * mn))) by (nonlinear_arith);
    assert((mn * mn) * (e2 * (bd * b2d)) == e2 * ((mn * bd) * (mn * b2d))) by (nonlinear_arith);

    // Spend both copies of the lower bound at once. This is the `md^2`.
    assert(mn * bd >= 0) by (nonlinear_arith)
        requires
            mn > 0,
            bd > 0,
    ;
    assert(mn * b2d >= 0) by (nonlinear_arith)
        requires
            mn > 0,
            b2d > 0,
    ;
    lemma_mul_le_mono2(mn * bd, mn * b2d, md * bn, md * b2n);
    lemma_mul_le_mono(e2, (mn * bd) * (mn * b2d), (md * bn) * (md * b2n));
    assert(e2 * ((md * bn) * (md * b2n)) == (e2 * (md * md)) * (bn * b2n)) by (nonlinear_arith);
}

/// **The quotient bound**: two `frac_diff_le` hypotheses compose through a
/// division, given a positive lower bound on both divisors.
///
/// The lower bound is a rational `m == mn/md`, supplied division-free as
/// `mn·bd <= md·bn` and `mn·b2d <= md·b2n` — i.e. `b >= m` and `b' >= m`. With
/// `|a| <= ca`, the conclusion is
///
/// ```text
/// |a/b - a'/b'| <= (ca·e2·md^2 + md·e1·mn^2) / (ed·mn^2)
/// ```
///
/// Callers with `b >= 1/2` pass `mn = 1, md = 2`, where this reads
/// `(4·ca·e2 + 2·e1)/ed`. The `md^2` on the divisor perturbation is real — see
/// [`lemma_recip_lipschitz_bound`] — and is why a near-zero divisor is
/// genuinely expensive rather than merely inconvenient.
///
/// The proof is *not* built on [`lemma_div_lipschitz`]'s identity. Division is
/// multiplication by the reciprocal, so this is
/// [`lemma_recip_lipschitz_bound`] fed into [`lemma_mul_lipschitz_bound`], and
/// that composition is both shorter and far cheaper for the solver than
/// attacking the four-way cross-multiplied difference head-on. The identity
/// lemma is left exactly as it was for the callers that use it directly.
///
/// Both divisors are required strictly positive rather than merely nonzero.
/// That is what keeps `ad·bn` and `a2d·b2n` positive, which `frac_diff_le`
/// needs; a two-sided version would have to case-split on the sign and is not
/// worth writing until something asks for it.
pub proof fn lemma_div_lipschitz_bound(
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
    ca: int,
    mn: int,
    md: int,
)
    requires
        ad > 0,
        bd > 0,
        a2d > 0,
        b2d > 0,
        ed > 0,
        bn > 0,
        b2n > 0,
        mn > 0,
        md > 0,
        e1 >= 0,
        e2 >= 0,
        ca >= 0,
        mn * bd <= md * bn,
        mn * b2d <= md * b2n,
        abs_int(an) <= ca * ad,
        frac_diff_le(an, ad, a2n, a2d, e1, ed),
        frac_diff_le(bn, bd, b2n, b2d, e2, ed),
    ensures
        frac_diff_le(
            an * bd,
            ad * bn,
            a2n * b2d,
            a2d * b2n,
            ca * (e2 * (md * md)) + md * (e1 * (mn * mn)),
            ed * (mn * mn),
        ),
{
    // Put both errors over the common denominator `ed·mn^2`: the reciprocal
    // bound already arrives there, so it is the dividend that gets rescaled.
    assert(mn * mn > 0) by (nonlinear_arith)
        requires
            mn > 0,
    ;
    assert(ed * (mn * mn) > 0) by (nonlinear_arith)
        requires
            ed > 0,
            mn > 0,
    ;
    lemma_frac_diff_scale(an, ad, a2n, a2d, e1, ed, mn * mn);
    lemma_recip_lipschitz_bound(bn, bd, b2n, b2d, e2, ed, mn, md);

    // The product bound bounds `|1/b'|`, not `|1/b|` — the primed side. From
    // `mn·b2d <= md·b2n` with `mn >= 1`, `b2d <= md·b2n`, so `md` serves.
    assert(b2d <= mn * b2d) by (nonlinear_arith)
        requires
            mn >= 1,
            b2d > 0,
    ;
    assert(abs_int(b2d) == b2d);
    assert(abs_int(b2d) <= md * b2n);

    // `a/b == a · (1/b)`. The reciprocal is passed as the second argument, so
    // its denominator is `bn` and its numerator `bd`.
    lemma_mul_lipschitz_bound(
        an,
        ad,
        bd,
        bn,
        a2n,
        a2d,
        b2d,
        b2n,
        e1 * (mn * mn),
        e2 * (md * md),
        ed * (mn * mn),
        ca,
        md,
    );
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
    assert(((e1 + e2) * (xd * zd)) * yd == (e1 * (xd * zd)) * yd + (e2 * (xd * zd)) * yd)
        by (nonlinear_arith);
    assert((e1 * (xd * yd)) * zd == (e1 * (xd * zd)) * yd) by (nonlinear_arith);
    assert((e2 * (yd * zd)) * xd == (e2 * (xd * zd)) * yd) by (nonlinear_arith);
    // The triangle inequality is on `|X|·yd`; the hypotheses are on `|A|·ee`
    // and `|B|·ee`. Scaling by `ee` is the step that joins them, and it is
    // nonlinear.
    assert(abs_int(xn * zd - zn * xd) * yd <= abs_int(xn * yd - yn * xd) * zd + abs_int(
        yn * zd - zn * yd,
    ) * xd);
    assert((abs_int(xn * zd - zn * xd) * yd) * ee <= (abs_int(xn * yd - yn * xd) * zd + abs_int(
        yn * zd - zn * yd,
    ) * xd) * ee) by (nonlinear_arith)
        requires
            ee > 0,
            abs_int(xn * zd - zn * xd) * yd <= abs_int(xn * yd - yn * xd) * zd + abs_int(
                yn * zd - zn * yd,
            ) * xd,
    ;
    assert((abs_int(xn * zd - zn * xd) * yd) * ee == (abs_int(xn * zd - zn * xd) * ee) * yd)
        by (nonlinear_arith);
    assert((abs_int(xn * yd - yn * xd) * zd + abs_int(yn * zd - zn * yd) * xd) * ee == (abs_int(
        xn * yd - yn * xd,
    ) * ee) * zd + (abs_int(yn * zd - zn * yd) * ee) * xd) by (nonlinear_arith);
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
    assert(pd * bd > 0) by (nonlinear_arith)
        requires
            pd > 0,
            bd > 0,
    ;
    assert(td > 0);
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
    // en·td - tn·ed, expanded: the two `bn` terms are the same monomial and
    // cancel, leaving bd^2 times the accumulator's own error.
    assert((an * bd + bn * ad) * (pd * bd) == (an * bd) * (pd * bd) + (bn * ad) * (pd * bd))
        by (nonlinear_arith);
    assert((pn * bd + bn * pd) * (ad * bd) == (pn * bd) * (ad * bd) + (bn * pd) * (ad * bd))
        by (nonlinear_arith);
    assert((bn * ad) * (pd * bd) == (bn * pd) * (ad * bd)) by (nonlinear_arith);
    assert((an * bd) * (pd * bd) == (bd * bd) * (an * pd)) by (nonlinear_arith);
    assert((pn * bd) * (ad * bd) == (bd * bd) * (pn * ad)) by (nonlinear_arith);
    assert((bd * bd) * (an * pd) - (bd * bd) * (pn * ad) == (bd * bd) * (an * pd - pn * ad))
        by (nonlinear_arith);
    assert(en * td - tn * ed == (bd * bd) * (an * pd - pn * ad));
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

/// The relative-error unit used throughout, as its reciprocal: `2^61`, so
/// that the bounds stay division-free.
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
