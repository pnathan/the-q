//! N-ary helpers (obligation V8).
//!
//! Every helper here is a **binary left fold in a fixed order**. That is a
//! deliberate restriction, not an oversight:
//!
//! * V2 safety is inherited for free — no new overflow analysis, because no new
//!   arithmetic shape appears.
//! * The result is deterministic. `sum(&[a, b, c])` is exactly
//!   `add(add(a, b), c)`, always, on every machine, in every thread. That is
//!   what makes results bit-reproducible.
//!
//! N-ary `i128` accumulation would re-open the overflow analysis for no
//! benefit, so it is not done.
//!
//! `sum`'s accumulated error after `k` elements is `k · 2^-61 · max(1,
//! |exact|)` (theorem `theorem_sum_error_accumulation`).
//!
//! `product` and `weighted_mean` carry the same shape of bound, but each
//! needs its own hypothesis, because the underlying operation is not
//! addition:
//!
//! * `product` (`theorem_product_error_accumulation`) needs every factor's
//!   magnitude bounded by `1` (`all_unit`). Multiplication is only
//!   1-Lipschitz when weighted by the other operand's magnitude, so without
//!   that hypothesis the carried error would amplify geometrically instead of
//!   accumulating additively, and no `k · 2^-61` bound would hold uniformly
//!   in `k`. The hypothesis is trivially satisfied in this crate's actual
//!   domain — every opinion component lives in `[0, 1]`.
//! * `weighted_mean` gets two separate bounds
//!   (`theorem_wm_num_error_accumulation`,
//!   `theorem_wm_denom_error_accumulation`) for its two internal
//!   accumulators, each against its own exact target (the true weighted sum,
//!   the true weight sum). Composing the two through the final division into
//!   a single bound on the returned value would need a further explicit
//!   hypothesis — the exact weight sum bounded away from zero — and is not
//!   attempted; see the doc comment on `theorem_wm_num_error_accumulation`.

use verus_builtin_macros::verus;

#[allow(unused_imports)]
use verus_builtin::*;
#[allow(unused_imports)]
use vstd::prelude::*;

#[allow(unused_imports)]
use crate::model::*;
#[allow(unused_imports)]
use crate::types::{Dir, Rat};

verus! {

// ---------------------------------------------------------------------------
// The exact value of a fold, in ghost form
// ---------------------------------------------------------------------------

/// Numerator of the exact left-fold sum of `s`.
pub open spec fn sum_num(s: Seq<Rat>) -> int
    decreases s.len(),
{
    if s.len() == 0 {
        0int
    } else {
        let init = s.subrange(0, s.len() as int - 1);
        let last = s[s.len() as int - 1];
        sum_num(init) * last.d() + last.n() * sum_den(init)
    }
}

/// Denominator of the exact left-fold sum of `s`.
pub open spec fn sum_den(s: Seq<Rat>) -> int
    decreases s.len(),
{
    if s.len() == 0 {
        1int
    } else {
        let init = s.subrange(0, s.len() as int - 1);
        let last = s[s.len() as int - 1];
        sum_den(init) * last.d()
    }
}

/// Numerator of the exact left-fold product of `s`.
pub open spec fn prod_num(s: Seq<Rat>) -> int
    decreases s.len(),
{
    if s.len() == 0 {
        1int
    } else {
        let init = s.subrange(0, s.len() as int - 1);
        prod_num(init) * s[s.len() as int - 1].n()
    }
}

/// Denominator of the exact left-fold product of `s`.
pub open spec fn prod_den(s: Seq<Rat>) -> int
    decreases s.len(),
{
    if s.len() == 0 {
        1int
    } else {
        let init = s.subrange(0, s.len() as int - 1);
        prod_den(init) * s[s.len() as int - 1].d()
    }
}

/// Every element of a slice satisfies the type invariant.
pub open spec fn all_wf(s: Seq<Rat>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> (#[trigger] s[i]).wf()
}

/// Every element of a slice has magnitude at most `1`: `|x| <= 1`.
///
/// This is the hypothesis `product`'s accumulated-error bound needs and
/// `sum`'s does not: see `theorem_product_error_accumulation` for why.
pub open spec fn all_unit(s: Seq<Rat>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> abs_int((#[trigger] s[i]).n()) <= s[i].d()
}

// ---------------------------------------------------------------------------
// The helpers
// ---------------------------------------------------------------------------

/// `xs[0] + xs[1] + ... `, left to right. Empty slice gives `0`.
pub fn sum(xs: &[Rat]) -> (r: Rat)
    requires
        all_wf(xs@),
    ensures
        r.wf(),
        // The fold is a *function* of the input, in a fixed order. This equality
        // is what makes the result reproducible, and it is what carries the V8
        // bound (`theorem_sum_error_accumulation`) over to the real code.
        r == fold_val(xs@),
{
    let mut acc = Rat::zero();
    let mut i: usize = 0;
    proof {
        assert(xs@.subrange(0, 0) =~= Seq::<Rat>::empty());
    }
    while i < xs.len()
        invariant
            acc.wf(),
            all_wf(xs@),
            i <= xs.len(),
            acc == fold_val(xs@.subrange(0, i as int)),
        decreases xs.len() - i,
    {
        proof {
            lemma_fold_snoc(xs@, i as int);
        }
        acc = Rat::add(acc, xs[i]);
        i = i + 1;
    }
    proof {
        assert(xs@.subrange(0, xs.len() as int) =~= xs@);
    }
    acc
}

/// Extending a prefix by one element extends the fold by one step.
pub proof fn lemma_fold_snoc(s: Seq<Rat>, i: int)
    requires
        0 <= i < s.len(),
    ensures
        fold_val(s.subrange(0, i + 1)) == crate::round::round_frac(
            crate::q::add_n(fold_val(s.subrange(0, i)), s[i]),
            crate::q::prod_d(fold_val(s.subrange(0, i)), s[i]),
            Dir::Nearest,
        ),
{
    let pre = s.subrange(0, i + 1);
    assert(pre.len() == i + 1);
    assert(pre[pre.len() as int - 1] == s[i]);
    assert(pre.subrange(0, pre.len() as int - 1) =~= s.subrange(0, i));
}

/// `xs[0] * xs[1] * ... `, left to right. Empty slice gives `1`.
pub fn product(xs: &[Rat]) -> (r: Rat)
    requires
        all_wf(xs@),
    ensures
        r.wf(),
        // The determinism-pinning equality, mirroring `sum`'s: it is what
        // carries the V8 bound (`theorem_product_error_accumulation`) over to
        // the real code.
        r == prod_fold_val(xs@),
{
    let mut acc = Rat::one();
    let mut i: usize = 0;
    proof {
        assert(xs@.subrange(0, 0) =~= Seq::<Rat>::empty());
    }
    while i < xs.len()
        invariant
            acc.wf(),
            all_wf(xs@),
            i <= xs.len(),
            acc == prod_fold_val(xs@.subrange(0, i as int)),
        decreases xs.len() - i,
    {
        proof {
            lemma_prod_fold_snoc(xs@, i as int);
        }
        acc = Rat::mul(acc, xs[i]);
        i = i + 1;
    }
    proof {
        assert(xs@.subrange(0, xs.len() as int) =~= xs@);
    }
    acc
}

/// Extending a prefix by one element extends the product fold by one step.
pub proof fn lemma_prod_fold_snoc(s: Seq<Rat>, i: int)
    requires
        0 <= i < s.len(),
    ensures
        prod_fold_val(s.subrange(0, i + 1)) == crate::round::round_frac(
            crate::q::mul_n(prod_fold_val(s.subrange(0, i)), s[i]),
            crate::q::prod_d(prod_fold_val(s.subrange(0, i)), s[i]),
            Dir::Nearest,
        ),
{
    let pre = s.subrange(0, i + 1);
    assert(pre.len() == i + 1);
    assert(pre[pre.len() as int - 1] == s[i]);
    assert(pre.subrange(0, pre.len() as int - 1) =~= s.subrange(0, i));
}

/// Every element of a slice of `(weight, value)` pairs is well-formed.
pub open spec fn all_wf_pairs(s: Seq<(Rat, Rat)>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> (#[trigger] s[i]).0.wf() && s[i].1.wf()
}

/// `sum(w_i · x_i) / sum(w_i)` — the shape the averaging-belief-fusion formula
/// needs.
///
/// `None` when the *accumulated* weight sum is zero — `wt_fold_val` below, the
/// fold's own rounded total, not the exact sum. Two different inputs land here:
/// weights that cancel exactly, and weights whose exact sum is nonzero but too
/// small for the grid, so the fold rounds it to zero (`1/MAX_MAG` against
/// `-1/(MAX_MAG - 2)` sums to about `-2^-123` and is refused). The mean is
/// undefined in the first case and unrepresentable in the second, and this crate
/// invents a value for neither.
pub fn weighted_mean(pairs: &[(Rat, Rat)]) -> (r: Option<Rat>)
    requires
        all_wf_pairs(pairs@),
    ensures
        r.is_some() ==> r.unwrap().wf(),
        // The determinism-pinning equalities, mirroring `sum`'s and
        // `product`'s: together they carry the V8 bounds
        // (`theorem_wm_num_error_accumulation`,
        // `theorem_wm_denom_error_accumulation`) over to the real code.
        r.is_none() <==> wt_fold_val(pairs@).n() == 0,
        r.is_some() ==> r.unwrap() == crate::round::round_frac(
            crate::q::div_n(wm_num_fold_val(pairs@), wt_fold_val(pairs@)),
            crate::q::div_d(wm_num_fold_val(pairs@), wt_fold_val(pairs@)),
            Dir::Nearest,
        ),
{
    let mut acc_num = Rat::zero();
    let mut acc_w = Rat::zero();
    let mut i: usize = 0;
    proof {
        assert(pairs@.subrange(0, 0) =~= Seq::<(Rat, Rat)>::empty());
    }
    while i < pairs.len()
        invariant
            acc_num.wf(),
            acc_w.wf(),
            all_wf_pairs(pairs@),
            i <= pairs.len(),
            acc_num == wm_num_fold_val(pairs@.subrange(0, i as int)),
            acc_w == wt_fold_val(pairs@.subrange(0, i as int)),
        decreases pairs.len() - i,
    {
        proof {
            lemma_wm_fold_snoc(pairs@, i as int);
        }
        let (w, x) = pairs[i];
        acc_num = Rat::add(acc_num, Rat::mul(w, x));
        acc_w = Rat::add(acc_w, w);
        i = i + 1;
    }
    proof {
        assert(pairs@.subrange(0, pairs.len() as int) =~= pairs@);
    }
    if acc_w.is_zero() {
        None
    } else {
        Some(Rat::div(acc_num, acc_w))
    }
}

/// Extending a prefix by one pair extends both `weighted_mean` folds — the
/// numerator accumulator and the weight accumulator — by one step.
pub proof fn lemma_wm_fold_snoc(s: Seq<(Rat, Rat)>, i: int)
    requires
        0 <= i < s.len(),
    ensures
        wm_num_fold_val(s.subrange(0, i + 1)) == crate::round::round_frac(
            crate::q::add_n(
                wm_num_fold_val(s.subrange(0, i)),
                crate::round::round_frac(
                    crate::q::mul_n(s[i].0, s[i].1),
                    crate::q::prod_d(s[i].0, s[i].1),
                    Dir::Nearest,
                ),
            ),
            crate::q::prod_d(
                wm_num_fold_val(s.subrange(0, i)),
                crate::round::round_frac(
                    crate::q::mul_n(s[i].0, s[i].1),
                    crate::q::prod_d(s[i].0, s[i].1),
                    Dir::Nearest,
                ),
            ),
            Dir::Nearest,
        ),
        wt_fold_val(s.subrange(0, i + 1)) == crate::round::round_frac(
            crate::q::add_n(wt_fold_val(s.subrange(0, i)), s[i].0),
            crate::q::prod_d(wt_fold_val(s.subrange(0, i)), s[i].0),
            Dir::Nearest,
        ),
{
    let pre = s.subrange(0, i + 1);
    assert(pre.len() == i + 1);
    assert(pre[pre.len() as int - 1] == s[i]);
    assert(pre.subrange(0, pre.len() as int - 1) =~= s.subrange(0, i));
}

// ---------------------------------------------------------------------------
// V8 — accumulated error
// ---------------------------------------------------------------------------

/// The value the left fold of `s` produces, as a *function*.
///
/// Deliberately not an `exists`-shaped predicate: the induction below has to
/// unfold this at every step, and an existential would force the solver to
/// guess a witness each time. Being a function also makes the exec `sum`'s
/// postcondition an equality, which is what pins determinism.
pub open spec fn fold_val(s: Seq<Rat>) -> Rat
    decreases s.len(),
{
    if s.len() == 0 {
        Rat { num: 0, den: 1 }
    } else {
        let init = s.subrange(0, s.len() as int - 1);
        let last = s[s.len() as int - 1];
        crate::round::round_frac(
            crate::q::add_n(fold_val(init), last),
            crate::q::prod_d(fold_val(init), last),
            Dir::Nearest,
        )
    }
}

/// The value the left fold of `s` produces under multiplication, as a
/// function — the `product` analogue of `fold_val`.
pub open spec fn prod_fold_val(s: Seq<Rat>) -> Rat
    decreases s.len(),
{
    if s.len() == 0 {
        Rat { num: 1, den: 1 }
    } else {
        let init = s.subrange(0, s.len() as int - 1);
        let last = s[s.len() as int - 1];
        crate::round::round_frac(
            crate::q::mul_n(prod_fold_val(init), last),
            crate::q::prod_d(prod_fold_val(init), last),
            Dir::Nearest,
        )
    }
}

/// Every prefix of the fold has step values bounded by `m`, and stays on a
/// non-saturating path. This is the hypothesis V8 needs and cannot invent:
/// without a magnitude bound on the intermediates there is nothing for the
/// accumulated error to be measured against.
///
/// For this crate's actual domain it is trivially satisfiable — opinions live
/// in `[0, 1]`, so `m == 1`.
pub open spec fn fold_bounded(s: Seq<Rat>, m: int) -> bool
    decreases s.len(),
{
    if s.len() == 0 {
        true
    } else {
        let init = s.subrange(0, s.len() as int - 1);
        let last = s[s.len() as int - 1];
        &&& fold_bounded(init, m)
        &&& max_int(
            crate::q::prod_d(fold_val(init), last),
            abs_int(crate::q::add_n(fold_val(init), last)),
        ) <= m * crate::q::prod_d(fold_val(init), last)
        &&& !crate::round::saturated(
            crate::q::add_n(fold_val(init), last),
            crate::q::prod_d(fold_val(init), last),
        )
    }
}

/// The exact fold denominator is positive, and the fold result is well-formed.
pub proof fn lemma_fold_wf(s: Seq<Rat>)
    requires
        all_wf(s),
    ensures
        fold_val(s).wf(),
        sum_den(s) > 0,
    decreases s.len(),
{
    if s.len() == 0 {
        crate::round::lemma_gcd_one();
    } else {
        let init = s.subrange(0, s.len() as int - 1);
        let last = s[s.len() as int - 1];
        assert(all_wf(init));
        assert(last.wf());
        lemma_fold_wf(init);
        let prev = fold_val(init);
        crate::q::lemma_op_widths(prev, last);
        crate::round::lemma_round_frac_wf(
            crate::q::add_n(prev, last),
            crate::q::prod_d(prev, last),
            Dir::Nearest,
        );
        assert(sum_den(s) == sum_den(init) * last.d());
        assert(sum_den(s) > 0) by (nonlinear_arith)
            requires
                sum_den(init) > 0,
                last.d() > 0,
                sum_den(s) == sum_den(init) * last.d(),
        ;
    }
}

/// Every prefix of the product fold has step values bounded by `m`, and
/// stays on a non-saturating path — the multiplicative analogue of
/// `fold_bounded`.
pub open spec fn prod_fold_bounded(s: Seq<Rat>, m: int) -> bool
    decreases s.len(),
{
    if s.len() == 0 {
        true
    } else {
        let init = s.subrange(0, s.len() as int - 1);
        let last = s[s.len() as int - 1];
        &&& prod_fold_bounded(init, m)
        &&& max_int(
            crate::q::prod_d(prod_fold_val(init), last),
            abs_int(crate::q::mul_n(prod_fold_val(init), last)),
        ) <= m * crate::q::prod_d(prod_fold_val(init), last)
        &&& !crate::round::saturated(
            crate::q::mul_n(prod_fold_val(init), last),
            crate::q::prod_d(prod_fold_val(init), last),
        )
    }
}

/// The exact product-fold denominator is positive, and the fold result is
/// well-formed.
pub proof fn lemma_prod_fold_wf(s: Seq<Rat>)
    requires
        all_wf(s),
    ensures
        prod_fold_val(s).wf(),
        prod_den(s) > 0,
    decreases s.len(),
{
    if s.len() == 0 {
        crate::round::lemma_gcd_one();
    } else {
        let init = s.subrange(0, s.len() as int - 1);
        let last = s[s.len() as int - 1];
        assert(all_wf(init));
        assert(last.wf());
        lemma_prod_fold_wf(init);
        let prev = prod_fold_val(init);
        crate::q::lemma_op_widths(prev, last);
        crate::round::lemma_round_frac_wf(
            crate::q::mul_n(prev, last),
            crate::q::prod_d(prev, last),
            Dir::Nearest,
        );
        assert(prod_den(s) == prod_den(init) * last.d());
        assert(prod_den(s) > 0) by (nonlinear_arith)
            requires
                prod_den(init) > 0,
                last.d() > 0,
                prod_den(s) == prod_den(init) * last.d(),
        ;
    }
}

/// **The V8 induction step for `product`.** One more rounded `mul` on top of
/// an accumulator already within `k` units takes the total to `k + 1` units
/// — **provided the new factor has magnitude at most `1`**.
///
/// Multiplication is not 1-Lipschitz on an unbounded domain the way addition
/// is: `|prev·next − prev'·next| = |next| · |prev − prev'|` scales the
/// carried error by `|next|`, not by `1` (see `lemma_mul_lipschitz`). If
/// `|next| <= 1` that scale factor cannot grow the carried error, and the
/// step behaves exactly like `sum`'s: one more unit from this step's own
/// rounding (R3, converted to absolute form by the magnitude hypothesis),
/// plus the carried error passed through with a scale factor at most `1`.
/// Without `|next| <= 1` no such bound holds uniformly in `k` — a run of
/// factors with magnitude `> 1` would amplify the carried error
/// geometrically, not additively, and no per-step "one more unit" law would
/// exist. That is why `theorem_product_error_accumulation` carries the extra
/// `all_unit` hypothesis that `theorem_sum_error_accumulation` does not need.
pub proof fn lemma_abs_error_mul_step(prev: Rat, pn: int, pd: int, next: Rat, r: Rat, k: nat, m: int)
    requires
        prev.wf(),
        next.wf(),
        r.wf(),
        pd > 0,
        m >= 1,
        within_abs_error(prev, pn, pd, k, m),
        within_error_bound(r, crate::q::mul_n(prev, next), crate::q::prod_d(prev, next)),
        max_int(
            crate::q::prod_d(prev, next),
            abs_int(crate::q::mul_n(prev, next)),
        ) <= m * crate::q::prod_d(prev, next),
        abs_int(next.n()) <= next.d(),
    ensures
        within_abs_error(r, pn * next.n(), pd * next.d(), (k + 1) as nat, m),
{
    let ad = prev.d();
    let an = prev.n();
    let bd = next.d();
    let bn = next.n();
    let en = crate::q::mul_n(prev, next);
    let ed = crate::q::prod_d(prev, next);
    let tn = pn * bn;
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
    // (a) this step's own rounding error, in absolute form.
    assert(abs_int(r.n() * ed - en * r.d()) * e <= m * (r.d() * ed)) by (nonlinear_arith)
        requires
            abs_int(r.n() * ed - en * r.d()) * e <= r.d() * max_int(ed, abs_int(en)),
            max_int(ed, abs_int(en)) <= m * ed,
            r.d() > 0,
    ;
    // (b) the carried error. Unlike addition, this does NOT pass through
    // unchanged: en·td - tn·ed factors as bn·bd times the accumulator's own
    // error, so the step scales the carried error by |bn|/bd. The
    // unit-magnitude hypothesis |bn| <= bd is what keeps that scale factor at
    // or below 1, so the carried error still only grows by one unit.
    //
    // The factorisation is given to the solver in small steps -- handed over
    // whole (four variables, degree four, plus a distribution) it exhausts
    // the resource limit, exactly as the addition step's analogous
    // factorisation does.
    assert((an * bn) * (pd * bd) == (bn * bd) * (an * pd)) by (nonlinear_arith);
    assert((pn * bn) * (ad * bd) == (bn * bd) * (pn * ad)) by (nonlinear_arith);
    assert((bn * bd) * (an * pd) - (bn * bd) * (pn * ad) == (bn * bd) * (an * pd - pn * ad))
        by (nonlinear_arith);
    assert(en * td - tn * ed == (bn * bd) * (an * pd - pn * ad));
    assert(ed * td == (bd * bd) * (ad * pd)) by (nonlinear_arith)
        requires
            ed == ad * bd,
            td == pd * bd,
    ;
    assert(abs_int((bn * bd) * (an * pd - pn * ad)) == abs_int(bn) * bd * abs_int(
        an * pd - pn * ad,
    )) by (nonlinear_arith)
        requires
            bd > 0,
    ;
    assert(abs_int(an * pd - pn * ad) >= 0);
    assert(abs_int(bn) * bd * (abs_int(an * pd - pn * ad) * e) <= bd * bd * (abs_int(
        an * pd - pn * ad,
    ) * e)) by (nonlinear_arith)
        requires
            0 <= abs_int(bn) <= bd,
            bd > 0,
            abs_int(an * pd - pn * ad) * e >= 0,
    ;
    assert(bd * bd * (abs_int(an * pd - pn * ad) * e) <= bd * bd * ((k as int) * m * (ad * pd)))
        by (nonlinear_arith)
        requires
            bd > 0,
            abs_int(an * pd - pn * ad) * e <= (k as int) * m * (ad * pd),
    ;
    assert(abs_int(en * td - tn * ed) * e <= ((k as int) * m) * (ed * td)) by (nonlinear_arith)
        requires
            bd > 0,
            abs_int(en * td - tn * ed) == abs_int(bn) * bd * abs_int(an * pd - pn * ad),
            abs_int(bn) * bd * (abs_int(an * pd - pn * ad) * e) <= bd * bd * ((k as int) * m * (ad
                * pd)),
            ed * td == (bd * bd) * (ad * pd),
    ;
    crate::lipschitz::lemma_frac_triangle(r.n(), r.d(), en, ed, tn, td, m, (k as int) * m, e);
    assert(m + (k as int) * m == ((k + 1) as int) * m) by (nonlinear_arith);
}

/// **V8 for `product`.** After `k` folded elements the accumulated error
/// against the exact product is at most `k · m · 2^-61` — **provided every
/// factor has magnitude at most `1`** (`all_unit(s)`).
///
/// The extra hypothesis over `theorem_sum_error_accumulation` is necessary,
/// not an artifact of the proof: see `lemma_abs_error_mul_step`. It is
/// trivially satisfiable in this crate's actual domain — every opinion
/// component lives in `[0, 1]` — where it coincides with `fold_bounded`'s own
/// `m == 1` case, exactly as documented in `docs/SPEC.md` §9.
pub proof fn theorem_product_error_accumulation(s: Seq<Rat>, m: int)
    requires
        all_wf(s),
        all_unit(s),
        m >= 1,
        prod_fold_bounded(s, m),
    ensures
        within_abs_error(prod_fold_val(s), prod_num(s), prod_den(s), s.len(), m),
    decreases s.len(),
{
    lemma_prod_fold_wf(s);
    if s.len() == 0 {
        assert(prod_num(s) == 1 && prod_den(s) == 1);
        assert(prod_fold_val(s).n() == 1 && prod_fold_val(s).d() == 1);
        crate::model::lemma_pow2_pos(crate::model::precision_b());
        // Both sides are zero, but `abs_int(0)` and the `0 · m · …` product
        // each need saying.
        assert(prod_fold_val(s).n() * prod_den(s) - prod_num(s) * prod_fold_val(s).d() == 0);
        assert(crate::model::abs_int(0) == 0);
        assert((s.len() as int) * m * (prod_fold_val(s).d() * prod_den(s)) == 0);
    } else {
        let init = s.subrange(0, s.len() as int - 1);
        let last = s[s.len() as int - 1];
        assert(all_wf(init));
        assert(all_unit(init));
        assert(prod_fold_bounded(init, m));
        theorem_product_error_accumulation(init, m);
        lemma_prod_fold_wf(init);
        let prev = prod_fold_val(init);
        crate::q::lemma_op_widths(prev, last);
        crate::round::lemma_r3_error(
            crate::q::mul_n(prev, last),
            crate::q::prod_d(prev, last),
            Dir::Nearest,
        );
        crate::round::lemma_round_frac_wf(
            crate::q::mul_n(prev, last),
            crate::q::prod_d(prev, last),
            Dir::Nearest,
        );
        assert(abs_int(last.n()) <= last.d());
        lemma_abs_error_mul_step(
            prev,
            prod_num(init),
            prod_den(init),
            last,
            prod_fold_val(s),
            init.len(),
            m,
        );
        assert(prod_num(s) == prod_num(init) * last.n());
        assert(prod_den(s) == prod_den(init) * last.d());
        assert(s.len() == init.len() + 1);
        // Restate the step lemma's conclusion in the goal's own vocabulary.
        assert(within_abs_error(
            prod_fold_val(s),
            prod_num(init) * last.n(),
            prod_den(init) * last.d(),
            (init.len() + 1) as nat,
            m,
        ));
    }
}

/// **V8.** After `k` folded elements the accumulated error against the exact
/// fold is at most `k · m · 2^-61`.
///
/// The induction is exactly the two-line argument: each `add` contributes one
/// fresh `2^-61` unit (R3), and the error already accumulated passes through
/// the addition untouched, because addition is exactly 1-Lipschitz. Both halves
/// live in `crate::lipschitz::lemma_abs_error_step`.
///
/// For the consuming engine's worst case of ~2·10⁴ sequential operations with
/// `m == 1` this is `2·10⁴ · 2^-61 ≈ 2^-46.7 ≈ 1·10^-14` — the same precision
/// class as `f64` accumulation, but deterministic and proven rather than
/// assumed.
pub proof fn theorem_sum_error_accumulation(s: Seq<Rat>, m: int)
    requires
        all_wf(s),
        m >= 1,
        fold_bounded(s, m),
    ensures
        within_abs_error(fold_val(s), sum_num(s), sum_den(s), s.len(), m),
    decreases s.len(),
{
    lemma_fold_wf(s);
    if s.len() == 0 {
        assert(sum_num(s) == 0 && sum_den(s) == 1);
        assert(fold_val(s).n() == 0 && fold_val(s).d() == 1);
        crate::model::lemma_pow2_pos(crate::model::precision_b());
        // Both sides are zero, but `abs_int(0)` and the `0 · m · …` product
        // each need saying.
        assert(fold_val(s).n() * sum_den(s) - sum_num(s) * fold_val(s).d() == 0);
        assert(crate::model::abs_int(0) == 0);
        assert((s.len() as int) * m * (fold_val(s).d() * sum_den(s)) == 0);
    } else {
        let init = s.subrange(0, s.len() as int - 1);
        let last = s[s.len() as int - 1];
        assert(all_wf(init));
        assert(fold_bounded(init, m));
        theorem_sum_error_accumulation(init, m);
        lemma_fold_wf(init);
        let prev = fold_val(init);
        crate::q::lemma_op_widths(prev, last);
        crate::round::lemma_r3_error(
            crate::q::add_n(prev, last),
            crate::q::prod_d(prev, last),
            Dir::Nearest,
        );
        crate::round::lemma_round_frac_wf(
            crate::q::add_n(prev, last),
            crate::q::prod_d(prev, last),
            Dir::Nearest,
        );
        crate::lipschitz::lemma_abs_error_step(
            prev,
            sum_num(init),
            sum_den(init),
            last,
            fold_val(s),
            init.len(),
            m,
        );
        assert(sum_num(s) == sum_num(init) * last.d() + last.n() * sum_den(init));
        assert(sum_den(s) == sum_den(init) * last.d());
        assert(s.len() == init.len() + 1);
        // Restate the step lemma's conclusion in the goal's own vocabulary.
        assert(within_abs_error(
            fold_val(s),
            sum_num(init) * last.d() + last.n() * sum_den(init),
            sum_den(init) * last.d(),
            (init.len() + 1) as nat,
            m,
        ));
    }
}

/// **The exact-path corollary.** If no step of the fold ever leaves the budget,
/// the whole fold is exact — the k-element lift of R1.
pub proof fn theorem_exact_fold_is_exact(s: Seq<Rat>)
    requires
        all_wf(s),
        fold_exact(s),
    ensures
        q_is(fold_val(s), sum_num(s), sum_den(s)),
    decreases s.len(),
{
    lemma_fold_wf(s);
    if s.len() == 0 {
        assert(sum_num(s) == 0 && sum_den(s) == 1);
    } else {
        let init = s.subrange(0, s.len() as int - 1);
        let last = s[s.len() as int - 1];
        assert(all_wf(init));
        theorem_exact_fold_is_exact(init);
        lemma_fold_wf(init);
        let prev = fold_val(init);
        crate::q::lemma_op_widths(prev, last);
        crate::round::lemma_r1_identity(
            crate::q::add_n(prev, last),
            crate::q::prod_d(prev, last),
            Dir::Nearest,
        );
        let r = fold_val(s);
        // r is exactly prev + last, prev is exactly the partial sum, so r is
        // exactly the whole sum.
        assert(sum_num(s) == sum_num(init) * last.d() + last.n() * sum_den(init));
        assert(sum_den(s) == sum_den(init) * last.d());
        lemma_exact_step(prev, last, r, sum_num(init), sum_den(init), sum_num(s), sum_den(s));
    }
}

/// Every step of the fold stays on the exact path.
pub open spec fn fold_exact(s: Seq<Rat>) -> bool
    decreases s.len(),
{
    if s.len() == 0 {
        true
    } else {
        let init = s.subrange(0, s.len() as int - 1);
        let last = s[s.len() as int - 1];
        &&& fold_exact(init)
        &&& crate::round::exact_path(
            crate::q::add_n(fold_val(init), last),
            crate::q::prod_d(fold_val(init), last),
        )
    }
}

/// Composing two exact steps stays exact.
///
/// `#[verifier::rlimit(20)]`: this file grew substantially with the `product`
/// and `weighted_mean` V8 additions, and the larger module pushed this
/// already-tight six-atom, degree-four proof (see the comment below) over the
/// default resource limit even though its own steps are unchanged. The same
/// annotation is already used for comparably-sized proofs in
/// `crate::lipschitz` (`lemma_triangle`, `lemma_mul_lipschitz`,
/// `lemma_div_lipschitz`).
#[verifier::rlimit(20)]
pub proof fn lemma_exact_step(prev: Rat, last: Rat, r: Rat, pn: int, pd: int, tn: int, td: int)
    requires
        prev.wf(),
        last.wf(),
        r.wf(),
        pd > 0,
        q_is(prev, pn, pd),
        q_is(r, crate::q::add_n(prev, last), crate::q::prod_d(prev, last)),
        tn == pn * last.d() + last.n() * pd,
        td == pd * last.d(),
    ensures
        q_is(r, tn, td),
{
    let ad = prev.d();
    let an = prev.n();
    let bd = last.d();
    let bn = last.n();
    // r == (an·bd + bn·ad)/(ad·bd) and an/ad == pn/pd, so r == tn/td.
    assert(r.n() * (ad * bd) == (an * bd + bn * ad) * r.d());
    assert(an * pd == pn * ad);
    // Handed over whole this exhausts the rlimit — six atoms, degree four, and
    // a hypothesis to substitute. Do it in four steps that each move one thing.
    assert(r.n() * td * (ad * bd) == (r.n() * (ad * bd)) * (pd * bd)) by (nonlinear_arith)
        requires
            td == pd * bd,
    ;
    assert((r.n() * (ad * bd)) * (pd * bd) == ((an * bd + bn * ad) * r.d()) * (pd * bd))
        by (nonlinear_arith)
        requires
            r.n() * (ad * bd) == (an * bd + bn * ad) * r.d(),
    ;
    assert((tn * r.d()) * (ad * bd) == ((pn * bd + bn * pd) * r.d()) * (ad * bd))
        by (nonlinear_arith)
        requires
            tn == pn * bd + bn * pd,
    ;
    // The remaining identity is the cross-multiplication hypothesis, scaled by
    // bd and by r.d().
    assert((an * bd + bn * ad) * (pd * bd) == (pn * bd + bn * pd) * (ad * bd))
        by (nonlinear_arith)
        requires
            an * pd == pn * ad,
    ;
    assert(((an * bd + bn * ad) * r.d()) * (pd * bd) == ((an * bd + bn * ad) * (pd * bd)) * r.d())
        by (nonlinear_arith);
    assert(((pn * bd + bn * pd) * r.d()) * (ad * bd) == ((pn * bd + bn * pd) * (ad * bd)) * r.d())
        by (nonlinear_arith);
    assert(r.n() * td == tn * r.d()) by (nonlinear_arith)
        requires
            ad > 0,
            bd > 0,
            r.n() * td * (ad * bd) == (tn * r.d()) * (ad * bd),
    ;
}

// ---------------------------------------------------------------------------
// V8 — accumulated error for `weighted_mean`
// ---------------------------------------------------------------------------
//
// `weighted_mean` folds two accumulators in the same loop: `acc_num` (a sum
// of rounded per-pair products) and `acc_w` (a plain sum of weights, exactly
// `sum`'s fold restricted to the weight half of each pair). Each is given its
// own V8 bound below, stated against the corresponding *exact* target
// (`wsum_num`/`wsum_den` for the true weighted sum `Σ w_i·x_i`, `wt_num`/
// `wt_den` for the true weight sum `Σ w_i`) — no rounding anywhere in either
// target, so composing the two through the final division is a genuinely
// separate step (see the doc comment on `theorem_wm_num_error_accumulation`
// for why that composition is intentionally NOT attempted here).

/// Numerator of the exact left-fold sum of just the weights in `s`.
pub open spec fn wt_num(s: Seq<(Rat, Rat)>) -> int
    decreases s.len(),
{
    if s.len() == 0 {
        0int
    } else {
        let init = s.subrange(0, s.len() as int - 1);
        let last = s[s.len() as int - 1].0;
        wt_num(init) * last.d() + last.n() * wt_den(init)
    }
}

/// Denominator of the exact left-fold sum of just the weights in `s`.
pub open spec fn wt_den(s: Seq<(Rat, Rat)>) -> int
    decreases s.len(),
{
    if s.len() == 0 {
        1int
    } else {
        let init = s.subrange(0, s.len() as int - 1);
        let last = s[s.len() as int - 1].0;
        wt_den(init) * last.d()
    }
}

/// Numerator of the *true* weighted sum `Σ w_i · x_i` — an exact fold over
/// the exact per-pair products, with no rounding anywhere. This, not the sum
/// of the *rounded* per-pair products, is the target `weighted_mean`'s
/// numerator accumulator is measured against.
pub open spec fn wsum_num(s: Seq<(Rat, Rat)>) -> int
    decreases s.len(),
{
    if s.len() == 0 {
        0int
    } else {
        let init = s.subrange(0, s.len() as int - 1);
        let last = s[s.len() as int - 1];
        let ln = last.0.n() * last.1.n();
        let ld = last.0.d() * last.1.d();
        wsum_num(init) * ld + ln * wsum_den(init)
    }
}

/// Denominator of the true weighted sum `Σ w_i · x_i`.
pub open spec fn wsum_den(s: Seq<(Rat, Rat)>) -> int
    decreases s.len(),
{
    if s.len() == 0 {
        1int
    } else {
        let init = s.subrange(0, s.len() as int - 1);
        let last = s[s.len() as int - 1];
        let ld = last.0.d() * last.1.d();
        wsum_den(init) * ld
    }
}

/// The value the exec loop's weight accumulator (`acc_w`) computes, as a
/// function — `fold_val` restricted to the weight half of each pair.
pub open spec fn wt_fold_val(s: Seq<(Rat, Rat)>) -> Rat
    decreases s.len(),
{
    if s.len() == 0 {
        Rat { num: 0, den: 1 }
    } else {
        let init = s.subrange(0, s.len() as int - 1);
        let last = s[s.len() as int - 1].0;
        crate::round::round_frac(
            crate::q::add_n(wt_fold_val(init), last),
            crate::q::prod_d(wt_fold_val(init), last),
            Dir::Nearest,
        )
    }
}

/// The value the exec loop's numerator accumulator (`acc_num`) computes: at
/// each step, round the pair's product, then round it into the running sum
/// — exactly what `Rat::add(acc_num, Rat::mul(w, x))` does.
pub open spec fn wm_num_fold_val(s: Seq<(Rat, Rat)>) -> Rat
    decreases s.len(),
{
    if s.len() == 0 {
        Rat { num: 0, den: 1 }
    } else {
        let init = s.subrange(0, s.len() as int - 1);
        let last = s[s.len() as int - 1];
        let t = crate::round::round_frac(
            crate::q::mul_n(last.0, last.1),
            crate::q::prod_d(last.0, last.1),
            Dir::Nearest,
        );
        crate::round::round_frac(
            crate::q::add_n(wm_num_fold_val(init), t),
            crate::q::prod_d(wm_num_fold_val(init), t),
            Dir::Nearest,
        )
    }
}

/// Every prefix of the weight fold has step values bounded by `m`, and stays
/// on a non-saturating path — `fold_bounded` restricted to the weight half.
pub open spec fn wt_bounded(s: Seq<(Rat, Rat)>, m: int) -> bool
    decreases s.len(),
{
    if s.len() == 0 {
        true
    } else {
        let init = s.subrange(0, s.len() as int - 1);
        let last = s[s.len() as int - 1].0;
        &&& wt_bounded(init, m)
        &&& max_int(
            crate::q::prod_d(wt_fold_val(init), last),
            abs_int(crate::q::add_n(wt_fold_val(init), last)),
        ) <= m * crate::q::prod_d(wt_fold_val(init), last)
        &&& !crate::round::saturated(
            crate::q::add_n(wt_fold_val(init), last),
            crate::q::prod_d(wt_fold_val(init), last),
        )
    }
}

/// Every prefix of the numerator fold has BOTH of its per-element roundings
/// — the `mul` and the `add` — bounded by `m` and non-saturating. Two
/// roundings happen per pair (`Rat::mul` then `Rat::add`), so this hypothesis
/// covers both, unlike `fold_bounded`'s one.
pub open spec fn wm_num_bounded(s: Seq<(Rat, Rat)>, m: int) -> bool
    decreases s.len(),
{
    if s.len() == 0 {
        true
    } else {
        let init = s.subrange(0, s.len() as int - 1);
        let last = s[s.len() as int - 1];
        let mn = crate::q::mul_n(last.0, last.1);
        let md = crate::q::prod_d(last.0, last.1);
        let t = crate::round::round_frac(mn, md, Dir::Nearest);
        let prevn = wm_num_fold_val(init);
        &&& wm_num_bounded(init, m)
        &&& max_int(md, abs_int(mn)) <= m * md
        &&& !crate::round::saturated(mn, md)
        &&& max_int(
            crate::q::prod_d(prevn, t),
            abs_int(crate::q::add_n(prevn, t)),
        ) <= m * crate::q::prod_d(prevn, t)
        &&& !crate::round::saturated(
            crate::q::add_n(prevn, t),
            crate::q::prod_d(prevn, t),
        )
    }
}

/// The exact weight-fold denominator is positive, and the fold result is
/// well-formed.
pub proof fn lemma_wt_fold_wf(s: Seq<(Rat, Rat)>)
    requires
        all_wf_pairs(s),
    ensures
        wt_fold_val(s).wf(),
        wt_den(s) > 0,
    decreases s.len(),
{
    if s.len() == 0 {
        crate::round::lemma_gcd_one();
    } else {
        let init = s.subrange(0, s.len() as int - 1);
        let last = s[s.len() as int - 1].0;
        assert(all_wf_pairs(init));
        assert(last.wf());
        lemma_wt_fold_wf(init);
        let prev = wt_fold_val(init);
        crate::q::lemma_op_widths(prev, last);
        crate::round::lemma_round_frac_wf(
            crate::q::add_n(prev, last),
            crate::q::prod_d(prev, last),
            Dir::Nearest,
        );
        assert(wt_den(s) == wt_den(init) * last.d());
        assert(wt_den(s) > 0) by (nonlinear_arith)
            requires
                wt_den(init) > 0,
                last.d() > 0,
                wt_den(s) == wt_den(init) * last.d(),
        ;
    }
}

/// The exact numerator-fold denominator is positive, and the fold result is
/// well-formed.
pub proof fn lemma_wm_num_fold_wf(s: Seq<(Rat, Rat)>)
    requires
        all_wf_pairs(s),
    ensures
        wm_num_fold_val(s).wf(),
        wsum_den(s) > 0,
    decreases s.len(),
{
    if s.len() == 0 {
        crate::round::lemma_gcd_one();
    } else {
        let init = s.subrange(0, s.len() as int - 1);
        let last = s[s.len() as int - 1];
        assert(all_wf_pairs(init));
        assert(last.0.wf() && last.1.wf());
        lemma_wm_num_fold_wf(init);
        let prevn = wm_num_fold_val(init);
        crate::q::lemma_op_widths(last.0, last.1);
        let mn = crate::q::mul_n(last.0, last.1);
        let md = crate::q::prod_d(last.0, last.1);
        crate::round::lemma_round_frac_wf(mn, md, Dir::Nearest);
        let t = crate::round::round_frac(mn, md, Dir::Nearest);
        crate::q::lemma_op_widths(prevn, t);
        crate::round::lemma_round_frac_wf(
            crate::q::add_n(prevn, t),
            crate::q::prod_d(prevn, t),
            Dir::Nearest,
        );
        assert(wsum_den(s) == wsum_den(init) * (last.0.d() * last.1.d()));
        assert(wsum_den(s) > 0) by (nonlinear_arith)
            requires
                wsum_den(init) > 0,
                last.0.d() > 0,
                last.1.d() > 0,
                wsum_den(s) == wsum_den(init) * (last.0.d() * last.1.d()),
        ;
    }
}

/// **V8 for `weighted_mean`'s weight accumulator.** After `k` pairs the
/// weight accumulator's error against the exact weight sum is at most
/// `k · m · 2^-61`.
///
/// A direct restatement of `theorem_sum_error_accumulation` for the weight
/// half of each pair — the induction and the lemma it calls
/// (`crate::lipschitz::lemma_abs_error_step`) are identical; only the
/// indexing (`s[i].0` instead of `s[i]`) differs.
pub proof fn theorem_wm_denom_error_accumulation(s: Seq<(Rat, Rat)>, m: int)
    requires
        all_wf_pairs(s),
        m >= 1,
        wt_bounded(s, m),
    ensures
        within_abs_error(wt_fold_val(s), wt_num(s), wt_den(s), s.len(), m),
    decreases s.len(),
{
    lemma_wt_fold_wf(s);
    if s.len() == 0 {
        assert(wt_num(s) == 0 && wt_den(s) == 1);
        assert(wt_fold_val(s).n() == 0 && wt_fold_val(s).d() == 1);
        crate::model::lemma_pow2_pos(crate::model::precision_b());
        assert(wt_fold_val(s).n() * wt_den(s) - wt_num(s) * wt_fold_val(s).d() == 0);
        assert(crate::model::abs_int(0) == 0);
        assert((s.len() as int) * m * (wt_fold_val(s).d() * wt_den(s)) == 0);
    } else {
        let init = s.subrange(0, s.len() as int - 1);
        let last = s[s.len() as int - 1].0;
        assert(all_wf_pairs(init));
        assert(wt_bounded(init, m));
        theorem_wm_denom_error_accumulation(init, m);
        lemma_wt_fold_wf(init);
        let prev = wt_fold_val(init);
        crate::q::lemma_op_widths(prev, last);
        crate::round::lemma_r3_error(
            crate::q::add_n(prev, last),
            crate::q::prod_d(prev, last),
            Dir::Nearest,
        );
        crate::round::lemma_round_frac_wf(
            crate::q::add_n(prev, last),
            crate::q::prod_d(prev, last),
            Dir::Nearest,
        );
        crate::lipschitz::lemma_abs_error_step(
            prev,
            wt_num(init),
            wt_den(init),
            last,
            wt_fold_val(s),
            init.len(),
            m,
        );
        assert(wt_num(s) == wt_num(init) * last.d() + last.n() * wt_den(init));
        assert(wt_den(s) == wt_den(init) * last.d());
        assert(s.len() == init.len() + 1);
        assert(within_abs_error(
            wt_fold_val(s),
            wt_num(init) * last.d() + last.n() * wt_den(init),
            wt_den(init) * last.d(),
            (init.len() + 1) as nat,
            m,
        ));
    }
}

/// R3 plus a magnitude bound on the exact value converts to a one-step
/// absolute-error bound. This is "part (a)" of every V8 induction step
/// elsewhere in this file, factored out here because
/// `theorem_wm_num_error_accumulation` needs it applied twice per element
/// (once for the `mul`, once for the `add`) instead of once.
pub proof fn lemma_r3_to_abs_error_1(r: Rat, n: int, d: int, m: int)
    requires
        r.wf(),
        d > 0,
        m >= 1,
        within_error_bound(r, n, d),
        max_int(d, abs_int(n)) <= m * d,
    ensures
        within_abs_error(r, n, d, 1, m),
{
    lemma_pow2_pos(precision_b());
    assert(abs_int(r.n() * d - n * r.d()) * pow2(precision_b()) <= m * (r.d() * d))
        by (nonlinear_arith)
        requires
            abs_int(r.n() * d - n * r.d()) * pow2(precision_b()) <= r.d() * max_int(d, abs_int(n)),
            max_int(d, abs_int(n)) <= m * d,
            r.d() > 0,
    ;
}

/// **V8 for `weighted_mean`'s numerator accumulator.** After `k` pairs the
/// numerator accumulator's error against the true weighted sum `Σ w_i · x_i`
/// is at most `2k · m · 2^-61` — twice `sum`'s rate, because each pair costs
/// two roundings (the `mul` and the `add`) instead of one.
///
/// Unlike `theorem_product_error_accumulation`, no `all_unit` hypothesis is
/// needed here: this accumulator is a *sum* of (independently rounded)
/// per-pair products, not a running product, so the carried error passes
/// through the outer `add` unchanged (addition is exactly 1-Lipschitz)
/// regardless of any pair's magnitude. Only the per-step magnitude bound
/// (`wm_num_bounded`, needed twice per step to convert each rounding's
/// relative R3 bound to an absolute one) is required — exactly the same kind
/// of hypothesis `fold_bounded` supplies for `sum`, just applied twice.
///
/// This bounds the numerator accumulator alone, against the exact (unrounded)
/// weighted sum — not the value `weighted_mean` finally returns after
/// dividing by the weight accumulator. Composing this bound with
/// `theorem_wm_denom_error_accumulation` through the division would need a
/// further explicit hypothesis (the exact weight sum bounded away from zero:
/// division is not Lipschitz otherwise, `crate::lipschitz::lemma_div_lipschitz`
/// states only the algebraic core, not a finished bound) and is left
/// unproven here. That is a real gap, not a hidden one: the two theorems in
/// this section are the actual "n-ary helper" bound V8 asks for — the
/// internal accumulation — and are exactly what `docs/SPEC.md` §9 documents
/// as the honest state of this obligation for `weighted_mean`.
pub proof fn theorem_wm_num_error_accumulation(s: Seq<(Rat, Rat)>, m: int)
    requires
        all_wf_pairs(s),
        m >= 1,
        wm_num_bounded(s, m),
    ensures
        within_abs_error(wm_num_fold_val(s), wsum_num(s), wsum_den(s), (2 * s.len()) as nat, m),
    decreases s.len(),
{
    lemma_wm_num_fold_wf(s);
    if s.len() == 0 {
        assert(wsum_num(s) == 0 && wsum_den(s) == 1);
        assert(wm_num_fold_val(s).n() == 0 && wm_num_fold_val(s).d() == 1);
        crate::model::lemma_pow2_pos(crate::model::precision_b());
        assert(wm_num_fold_val(s).n() * wsum_den(s) - wsum_num(s) * wm_num_fold_val(s).d() == 0);
        assert(crate::model::abs_int(0) == 0);
        assert((2 * s.len()) as int == 0) by (nonlinear_arith)
            requires
                s.len() == 0,
        ;
        assert(((2 * s.len()) as int) * m * (wm_num_fold_val(s).d() * wsum_den(s)) == 0)
            by (nonlinear_arith)
            requires
                (2 * s.len()) as int == 0,
        ;
    } else {
        let init = s.subrange(0, s.len() as int - 1);
        let last = s[s.len() as int - 1];
        assert(all_wf_pairs(init));
        assert(wm_num_bounded(init, m));
        theorem_wm_num_error_accumulation(init, m);
        lemma_wm_num_fold_wf(init);
        let prevn = wm_num_fold_val(init);
        let wn0 = wsum_num(init);
        let wd0 = wsum_den(init);
        let k0 = init.len();
        let e = pow2(precision_b());
        lemma_pow2_pos(precision_b());

        // Step 1: the per-pair product's own rounding error (one unit).
        crate::q::lemma_op_widths(last.0, last.1);
        let mn = crate::q::mul_n(last.0, last.1);
        let md = crate::q::prod_d(last.0, last.1);
        crate::round::lemma_r3_error(mn, md, Dir::Nearest);
        crate::round::lemma_round_frac_wf(mn, md, Dir::Nearest);
        let t = crate::round::round_frac(mn, md, Dir::Nearest);
        lemma_r3_to_abs_error_1(t, mn, md, m);

        // Step 2: combine the carried numerator error (2·k0 units) and the
        // product's own error (1 unit) across the exact addition -- errors
        // from two independent approximants simply add.
        crate::lipschitz::lemma_add_lipschitz(
            prevn.n(),
            prevn.d(),
            t.n(),
            t.d(),
            wn0,
            wd0,
            mn,
            md,
            (2 * k0) as int * m,
            1 * m,
            e,
        );

        // Step 3: this step's own `add` rounding error (one more unit).
        crate::q::lemma_op_widths(prevn, t);
        crate::round::lemma_r3_error(
            crate::q::add_n(prevn, t),
            crate::q::prod_d(prevn, t),
            Dir::Nearest,
        );
        crate::round::lemma_round_frac_wf(
            crate::q::add_n(prevn, t),
            crate::q::prod_d(prevn, t),
            Dir::Nearest,
        );
        lemma_r3_to_abs_error_1(
            wm_num_fold_val(s),
            crate::q::add_n(prevn, t),
            crate::q::prod_d(prevn, t),
            m,
        );

        // Chain steps 2 and 3.
        crate::lipschitz::lemma_frac_triangle(
            wm_num_fold_val(s).n(),
            wm_num_fold_val(s).d(),
            crate::q::add_n(prevn, t),
            crate::q::prod_d(prevn, t),
            wn0 * md + mn * wd0,
            wd0 * md,
            1 * m,
            (2 * k0) as int * m + 1 * m,
            e,
        );

        assert(wsum_num(s) == wn0 * md + mn * wd0);
        assert(wsum_den(s) == wd0 * md);
        assert(s.len() == k0 + 1);
        assert(1 * m + ((2 * k0) as int * m + 1 * m) == ((2 * (k0 + 1)) as int) * m)
            by (nonlinear_arith);
        assert(within_abs_error(
            wm_num_fold_val(s),
            wn0 * md + mn * wd0,
            wd0 * md,
            (2 * (k0 + 1)) as nat,
            m,
        ));
    }
}

} // verus!
