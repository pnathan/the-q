//! N-ary helpers (V8): `sum`, `product`, `weighted_mean`.
//!
//! Each is a binary left fold in a fixed order, so V2 safety is inherited and
//! results are bit-reproducible. After `k` elements `sum` is within
//! `k · m · 2^-61` of the exact fold, with `m` bounding the intermediates
//! (`theorem_sum_error_accumulation`); `product` has the same bound under
//! `all_unit` (`theorem_product_error_accumulation`), since a factor above 1
//! amplifies carried error geometrically; `weighted_mean`'s two accumulators
//! are bounded separately, and `theorem_weighted_mean_return_error` composes
//! them through the division into `8 · k · delta_den / (delta_num · 2^61)` on
//! the returned value, given weights and values in `[0, 1]` and an exact
//! weight sum of at least `delta_num / delta_den`.

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
/// `product`'s accumulated-error bound needs this hypothesis. `sum`'s bound
/// does not. See `theorem_product_error_accumulation` for the reason.
pub open spec fn all_unit(s: Seq<Rat>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> abs_int((#[trigger] s[i]).n()) <= s[i].d()
}

// ---------------------------------------------------------------------------
// The helpers
// ---------------------------------------------------------------------------

/// `xs[0] + xs[1] + ... `, left to right. Empty slice gives `0`.
///
/// ```
/// use the_q::Rat;
/// use the_q::nary;
///
/// let xs = [Rat::one(), Rat::one(), Rat::new(1, 2).unwrap()];
/// assert_eq!(nary::sum(&xs), Rat::new(5, 2).unwrap());
/// assert_eq!(nary::sum(&[]), Rat::zero());
/// ```
pub fn sum(xs: &[Rat]) -> (r: Rat)
    requires
        all_wf(xs@),
    ensures
        r.wf(),
        // The fold is a *function* of the input, in a fixed order. This equality
        // makes the result reproducible. It also carries the V8 bound
        // (`theorem_sum_error_accumulation`) over to the real code.
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
///
/// ```
/// use the_q::Rat;
/// use the_q::nary;
///
/// let xs = [Rat::new(1, 2).unwrap(), Rat::new(2, 3).unwrap()];
/// assert_eq!(nary::product(&xs), Rat::new(1, 3).unwrap());
/// assert_eq!(nary::product(&[]), Rat::one());
/// ```
pub fn product(xs: &[Rat]) -> (r: Rat)
    requires
        all_wf(xs@),
    ensures
        r.wf(),
        // The determinism-pinning equality mirrors `sum`'s. It carries the V8
        // bound (`theorem_product_error_accumulation`) over to the real code.
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

/// Every weight and value is in the closed unit interval.
///
/// This is the natural domain of subjective-logic averaging and is the
/// relational fact needed by the returned-value error theorem: for
/// nonnegative weights and unit values, `0 <= sum(w*x) <= sum(w)`.
pub open spec fn all_unit_pairs(s: Seq<(Rat, Rat)>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> {
        let p = #[trigger] s[i];
        &&& 0 <= p.0.n()
        &&& p.0.n() <= p.0.d()
        &&& 0 <= p.1.n()
        &&& p.1.n() <= p.1.d()
    }
}

/// `sum(w_i · x_i) / sum(w_i)`; `None` when the *rounded* weight sum is zero,
/// whether the weights cancel or their sum is below the grid.
///
/// ```
/// use the_q::Rat;
/// use the_q::nary;
///
/// let pairs = [
///     (Rat::one(), Rat::zero()),
///     (Rat::one(), Rat::new(2, 1).unwrap()),
/// ];
/// assert_eq!(nary::weighted_mean(&pairs), Some(Rat::one()));
/// assert_eq!(nary::weighted_mean(&[]), None);
/// ```
pub fn weighted_mean(pairs: &[(Rat, Rat)]) -> (r: Option<Rat>)
    requires
        all_wf_pairs(pairs@),
    ensures
        r.is_some() ==> r.unwrap().wf(),
        // The determinism-pinning equalities mirror `sum`'s and `product`'s.
        // Together they carry the V8 bounds
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

/// Extending a prefix by one pair extends both `weighted_mean` folds by one
/// step. The two folds are the numerator accumulator and the weight
/// accumulator.
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

/// The value of the left fold of `s`, as a function so the exec `sum`'s
/// postcondition is an equality.
pub open spec fn fold_val(s: Seq<Rat>) -> Rat
    decreases s.len(),
{
    if s.len() == 0 {
        Rat::from_raw_spec(0, 1)
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
/// function. This is the `product` analogue of `fold_val`.
pub open spec fn prod_fold_val(s: Seq<Rat>) -> Rat
    decreases s.len(),
{
    if s.len() == 0 {
        Rat::from_raw_spec(1, 1)
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

/// Every prefix of the fold is bounded by `m` and non-saturating; the
/// hypothesis V8 measures error against.
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
        Rat::lemma_from_raw_spec_components(0, 1);
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
/// stays on a non-saturating path. This is the multiplicative analogue of
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
        Rat::lemma_from_raw_spec_components(1, 1);
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

/// V8 induction step for `product`, under `|next| <= 1`: the carried error is
/// scaled by `|next|` (`|prev·next − prev'·next| = |next| · |prev − prev'|`),
/// so a unit factor passes it through and the step costs one more R3 unit. A
/// factor above 1 would amplify geometrically; hence `all_unit`.
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
    // unchanged. The term en·td - tn·ed factors as bn·bd times the
    // accumulator's own error, thus the step scales the carried error by
    // |bn|/bd. The unit-magnitude hypothesis |bn| <= bd keeps that scale factor
    // at or below 1, thus the carried error still only grows by one unit.
    //
    // The factorisation goes to the solver in small steps. Handed over whole
    // (four variables, degree four, plus a distribution) it exhausts the
    // resource limit, exactly as the addition step's analogous factorisation
    // does.
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

/// V8 for `product`: within `k · m · 2^-61` of the exact product, given
/// `all_unit(s)`; see `lemma_abs_error_mul_step` for why that is necessary.
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
        Rat::lemma_from_raw_spec_components(1, 1);
        assert(prod_num(s) == 1 && prod_den(s) == 1);
        assert(prod_fold_val(s).n() == 1 && prod_fold_val(s).d() == 1);
        crate::model::lemma_pow2_pos(crate::model::precision_b());
        // Both sides are zero. The solver still needs `abs_int(0)` and the
        // `0 · m · …` product stated explicitly.
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

/// V8: after `k` folded elements the error against the exact fold is at most
/// `k · m · 2^-61`. Induction by `crate::lipschitz::lemma_abs_error_step`.
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
        Rat::lemma_from_raw_spec_components(0, 1);
        assert(sum_num(s) == 0 && sum_den(s) == 1);
        assert(fold_val(s).n() == 0 && fold_val(s).d() == 1);
        crate::model::lemma_pow2_pos(crate::model::precision_b());
        // Both sides are zero. The solver still needs `abs_int(0)` and the
        // `0 · m · …` product stated explicitly.
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

/// **The exact-path corollary.** If no step of the fold leaves the budget, the
/// whole fold is exact. This is the k-element lift of R1.
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
        Rat::lemma_from_raw_spec_components(0, 1);
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
        // r is exactly prev + last, and prev is exactly the partial sum. Thus r
        // is exactly the whole sum.
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

/// Composing two exact steps stays exact. `rlimit` raised: a six-atom,
/// degree-four identity at this module size.
#[verifier::rlimit(40)]
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
    // Handed over whole this exhausts the rlimit. It has six atoms, degree
    // four, and a hypothesis to substitute. Four steps each move one thing.
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
    // The remaining identity is the cross-multiplication hypothesis. It is
    // scaled by bd and by r.d().
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
// Two accumulators in one loop: `acc_num`, a sum of rounded products, and
// `acc_w`, `sum`'s fold on the weights. Each is bounded against its exact
// target below; `theorem_weighted_mean_return_error` composes them.

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

/// Numerator of the *true* weighted sum `Σ w_i · x_i`. It is an exact fold
/// over the exact per-pair products, with no rounding anywhere. This value is
/// the target for `weighted_mean`'s numerator accumulator, rather than the sum
/// of the *rounded* per-pair products.
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
/// function. It is `fold_val` restricted to the weight half of each pair.
pub open spec fn wt_fold_val(s: Seq<(Rat, Rat)>) -> Rat
    decreases s.len(),
{
    if s.len() == 0 {
        Rat::from_raw_spec(0, 1)
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

/// The value the exec loop's numerator accumulator (`acc_num`) computes. At
/// each step it rounds the pair's product, then rounds that into the running
/// sum. This is exactly what `Rat::add(acc_num, Rat::mul(w, x))` does.
pub open spec fn wm_num_fold_val(s: Seq<(Rat, Rat)>) -> Rat
    decreases s.len(),
{
    if s.len() == 0 {
        Rat::from_raw_spec(0, 1)
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
/// on a non-saturating path. It is `fold_bounded` restricted to the weight
/// half.
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
/// bounded by `m` and non-saturating. The two roundings are the `mul` and the
/// `add`. Each pair costs two roundings (`Rat::mul` then `Rat::add`), thus
/// this hypothesis covers both. `fold_bounded` covers one.
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
        Rat::lemma_from_raw_spec_components(0, 1);
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
        Rat::lemma_from_raw_spec_components(0, 1);
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

/// For nonnegative weights and values in `[0,1]`, the exact weighted
/// numerator is itself nonnegative and is no greater than the exact weight
/// sum.  The comparison is division-free because the two exact folds use
/// different (positive) denominators.
proof fn lemma_reorder_ab_cd_to_db_ac(a: int, b: int, c: int, d: int)
    ensures
        (a * b) * (c * d) == (d * b) * (a * c),
{
    assert((a * b) * (c * d) == (d * b) * (a * c)) by (nonlinear_arith);
}

proof fn lemma_reorder_ab_cd_to_acd_b(a: int, b: int, c: int, d: int)
    ensures
        (a * b) * (c * d) == ((a * c) * d) * b,
{
    assert((a * b) * (c * d) == ((a * c) * d) * b) by (nonlinear_arith);
}

#[verifier::rlimit(30)]
pub proof fn lemma_wm_exact_numerator_le_denominator(s: Seq<(Rat, Rat)>)
    requires
        all_wf_pairs(s),
        all_unit_pairs(s),
    ensures
        0 <= wsum_num(s),
        0 <= wt_num(s),
        wsum_num(s) * wt_den(s) <= wt_num(s) * wsum_den(s),
        wt_num(s) <= (s.len() as int) * wt_den(s),
        wsum_den(s) > 0,
        wt_den(s) > 0,
    decreases s.len(),
{
    lemma_wm_num_fold_wf(s);
    lemma_wt_fold_wf(s);
    if s.len() == 0 {
    } else {
        let init = s.subrange(0, s.len() as int - 1);
        let last = s[s.len() as int - 1];
        let w = last.0;
        let x = last.1;
        assert(all_wf_pairs(init));
        assert(all_unit_pairs(init));
        assert(0 <= w.n() && w.n() <= w.d());
        assert(0 <= x.n() && x.n() <= x.d());
        lemma_wm_exact_numerator_le_denominator(init);

        let an = wsum_num(init);
        let ad = wsum_den(init);
        let bn = wt_num(init);
        let bd = wt_den(init);
        let wn = w.n();
        let wd = w.d();
        let xn = x.n();
        let xd = x.d();

        assert(wsum_num(s) == an * (wd * xd) + (wn * xn) * ad);
        assert(wsum_den(s) == ad * (wd * xd));
        assert(wt_num(s) == bn * wd + wn * bd);
        assert(wt_den(s) == bd * wd);

        assert(0 <= an * (wd * xd)) by (nonlinear_arith)
            requires an >= 0, wd > 0, xd > 0;
        assert(0 <= (wn * xn) * ad) by (nonlinear_arith)
            requires wn >= 0, xn >= 0, ad > 0;
        assert(0 <= wsum_num(s));
        assert(0 <= bn * wd) by (nonlinear_arith)
            requires bn >= 0, wd > 0;
        assert(0 <= wn * bd) by (nonlinear_arith)
            requires wn >= 0, bd > 0;
        assert(0 <= wt_num(s));

        // The old weighted numerator is below the old weight sum.  Scale
        // that inequality by the positive denominator contribution of the
        // new pair.
        crate::lipschitz::lemma_mul_le_mono(wd * wd * xd, an * bd, bn * ad);
        assert((wd * wd * xd) * (an * bd) <= (wd * wd * xd) * (bn * ad));

        // The new contribution satisfies w*x <= w because x <= 1.
        crate::lipschitz::lemma_mul_le_mono(wn * ad * bd * wd, xn, xd);
        assert((wn * ad * bd * wd) * xn <= (wn * ad * bd * wd) * xd);

        // Adding those two scaled inequalities is exactly the desired
        // cross-multiplied comparison for the extended folds.
        let wl = an * (wd * xd);
        let wc = (wn * xn) * ad;
        let dl = bn * wd;
        let dc = wn * bd;
        let wz = bd * wd;
        let dz = ad * (wd * xd);
        vstd::arithmetic::mul::lemma_mul_is_distributive_add_other_way(wz, wl, wc);
        vstd::arithmetic::mul::lemma_mul_is_distributive_add_other_way(dz, dl, dc);

        lemma_reorder_ab_cd_to_db_ac(an, wd * xd, bd, wd);
        vstd::arithmetic::mul::lemma_mul_is_associative(wd, wd, xd);
        assert(wl * wz == (wd * wd * xd) * (an * bd));

        lemma_reorder_ab_cd_to_acd_b(wn, xn, ad, bd * wd);
        vstd::arithmetic::mul::lemma_mul_is_associative(wn * xn, ad, bd * wd);
        assert(wc * wz == ((wn * ad) * (bd * wd)) * xn);
        vstd::arithmetic::mul::lemma_mul_is_associative(wn * ad, bd, wd);
        assert((wn * ad) * (bd * wd) == wn * ad * bd * wd);
        assert(wc * wz == (wn * ad * bd * wd) * xn);

        lemma_reorder_ab_cd_to_db_ac(bn, wd, ad, wd * xd);
        vstd::arithmetic::mul::lemma_mul_is_associative(wd, wd, xd);
        assert(dl * dz == (wd * wd * xd) * (bn * ad));

        lemma_reorder_ab_cd_to_acd_b(wn, bd, ad, wd * xd);
        vstd::arithmetic::mul::lemma_mul_is_associative(wn * ad, wd, xd);
        assert(dc * dz == (wn * ad * wd * xd) * bd);
        assert((wn * ad * wd * xd) * bd == (wn * ad * bd * wd) * xd)
            by (nonlinear_arith);

        assert(wsum_num(s) * wt_den(s) == wl * wz + wc * wz);
        assert(wt_num(s) * wsum_den(s) == dl * dz + dc * dz);

        assert(bn * wd <= (init.len() as int) * bd * wd) by (nonlinear_arith)
            requires
                bn <= (init.len() as int) * bd,
                wd > 0,
        ;
        assert(wn * bd <= wd * bd) by (nonlinear_arith)
            requires
                wn <= wd,
                bd > 0,
        ;
        assert(s.len() == init.len() + 1);
        assert(wt_num(s) <= (s.len() as int) * wt_den(s)) by (nonlinear_arith)
            requires
                wt_num(s) == bn * wd + wn * bd,
                wt_den(s) == bd * wd,
                bn * wd <= (init.len() as int) * bd * wd,
                wn * bd <= wd * bd,
                s.len() == init.len() + 1,
        ;
    }
}

/// V8 for the weight accumulator: within `k · m · 2^-61` of `Σ w_i`;
/// `theorem_sum_error_accumulation` on the weight half of each pair.
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
        Rat::lemma_from_raw_spec_components(0, 1);
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

/// If the exact weight sum is at least `delta` and the accumulated weight
/// error is at most `delta/2`, then the rounded denominator is at least
/// `delta/2` as well.  All comparisons are cross-multiplied.
pub proof fn lemma_wm_rounded_denominator_positive(
    s: Seq<(Rat, Rat)>,
    delta_num: int,
    delta_den: int,
)
    requires
        all_wf_pairs(s),
        delta_num > 0,
        delta_den > 0,
        delta_num * wt_den(s) <= delta_den * wt_num(s),
        within_abs_error(wt_fold_val(s), wt_num(s), wt_den(s), s.len(), 1),
        2 * (s.len() as int) * delta_den <= delta_num * pow2(precision_b()),
    ensures
        wt_fold_val(s).n() > 0,
        delta_num * wt_fold_val(s).d()
            <= 2 * delta_den * wt_fold_val(s).n(),
{
    lemma_wt_fold_wf(s);
    lemma_pow2_pos(precision_b());
    let b = wt_fold_val(s);
    let bn = wt_num(s);
    let bd = wt_den(s);
    let k = s.len() as int;
    let e = pow2(precision_b());
    let z = b.n() * bd - bn * b.d();

    assert(abs_int(z) * e <= k * (b.d() * bd));
    assert(0 <= abs_int(z));
    assert(-abs_int(z) <= z);

    assert((2 * delta_den) * (abs_int(z) * e)
        <= (2 * delta_den) * (k * (b.d() * bd))) by (nonlinear_arith)
        requires
            delta_den > 0,
            abs_int(z) * e <= k * (b.d() * bd),
    ;
    assert((2 * delta_den) * (k * (b.d() * bd))
        <= (delta_num * e) * (b.d() * bd)) by (nonlinear_arith)
        requires
            2 * k * delta_den <= delta_num * e,
            b.d() > 0,
            bd > 0,
    ;
    assert(2 * delta_den * abs_int(z) <= delta_num * b.d() * bd)
        by (nonlinear_arith)
        requires
            e > 0,
            (2 * delta_den) * (abs_int(z) * e)
                <= (delta_num * e) * (b.d() * bd),
    ;
    assert(delta_num * b.d() * bd <= delta_den * bn * b.d())
        by (nonlinear_arith)
        requires
            delta_num * bd <= delta_den * bn,
            b.d() > 0,
    ;
    assert(2 * delta_den * abs_int(z) <= delta_den * bn * b.d());
    assert(2 * abs_int(z) <= bn * b.d()) by (nonlinear_arith)
        requires
            delta_den > 0,
            2 * delta_den * abs_int(z) <= delta_den * bn * b.d(),
    ;
    assert(bn * b.d() - b.n() * bd <= abs_int(z));
    assert(bn * b.d() <= 2 * b.n() * bd) by (nonlinear_arith)
        requires
            2 * abs_int(z) <= bn * b.d(),
            bn * b.d() - b.n() * bd <= abs_int(z),
    ;
    assert(delta_num * b.d() * bd <= 2 * delta_den * b.n() * bd)
        by (nonlinear_arith)
        requires
            delta_num * bd <= delta_den * bn,
            b.d() > 0,
            bn * b.d() <= 2 * b.n() * bd,
            delta_den > 0,
    ;
    assert(delta_num * b.d() <= 2 * delta_den * b.n()) by (nonlinear_arith)
        requires
            bd > 0,
            delta_num * b.d() * bd <= 2 * delta_den * b.n() * bd,
    ;
    assert(b.n() > 0) by (nonlinear_arith)
        requires
            delta_num > 0,
            b.d() > 0,
            delta_den > 0,
            delta_num * b.d() <= 2 * delta_den * b.n(),
    ;
}

/// Compose the two accumulator bounds through the exact final quotient. The
/// relation `0 <= Σ w·x <= Σ w` replaces the generic numerator magnitude bound
/// and removes a factor of `k`; pre-rounding bound `6k/(delta · 2^61)`.
#[verifier::rlimit(30)]
pub proof fn lemma_wm_return_bound_composition(
    s: Seq<(Rat, Rat)>,
    delta_num: int,
    delta_den: int,
)
    requires
        all_wf_pairs(s),
        all_unit_pairs(s),
        delta_num > 0,
        delta_den > 0,
        delta_num * wt_den(s) <= delta_den * wt_num(s),
        within_abs_error(wm_num_fold_val(s), wsum_num(s), wsum_den(s), (2 * s.len()) as nat, 1),
        within_abs_error(wt_fold_val(s), wt_num(s), wt_den(s), s.len(), 1),
        2 * (s.len() as int) * delta_den <= delta_num * pow2(precision_b()),
    ensures
        wt_fold_val(s).n() > 0,
        crate::q::div_d(wm_num_fold_val(s), wt_fold_val(s)) > 0,
        max_int(
            crate::q::div_d(wm_num_fold_val(s), wt_fold_val(s)),
            abs_int(crate::q::div_n(wm_num_fold_val(s), wt_fold_val(s))),
        ) <= 4 * crate::q::div_d(wm_num_fold_val(s), wt_fold_val(s)),
        crate::lipschitz::frac_diff_le(
            crate::q::div_n(wm_num_fold_val(s), wt_fold_val(s)),
            crate::q::div_d(wm_num_fold_val(s), wt_fold_val(s)),
            wsum_num(s) * wt_den(s),
            wsum_den(s) * wt_num(s),
            6 * (s.len() as int) * delta_den,
            delta_num * pow2(precision_b()),
        ),
{
    lemma_wm_num_fold_wf(s);
    lemma_wt_fold_wf(s);
    lemma_wm_exact_numerator_le_denominator(s);
    lemma_wm_rounded_denominator_positive(s, delta_num, delta_den);

    let a = wm_num_fold_val(s);
    let b = wt_fold_val(s);
    let an = wsum_num(s);
    let ad = wsum_den(s);
    let bn = wt_num(s);
    let bd = wt_den(s);
    let k = s.len() as int;
    let e = pow2(precision_b());
    let p = a.n() * ad - an * a.d();
    let q = b.n() * bd - bn * b.d();
    let x = crate::q::div_n(a, b) * (ad * bn)
        - (an * bd) * crate::q::div_d(a, b);

    lemma_pow2_pos(precision_b());
    assert(e > 0);

    assert(crate::q::div_n(a, b) == a.n() * b.d());
    assert(crate::q::div_d(a, b) == a.d() * b.n());
    assert(bn > 0) by (nonlinear_arith)
        requires
            delta_num > 0,
            bd > 0,
            delta_den > 0,
            delta_num * bd <= delta_den * bn,
    ;
    assert(k > 0) by {
        if k <= 0 {
            assert(s.len() == 0);
            assert(wt_num(s) == 0);
            assert(wt_den(s) == 1);
            assert(false) by (nonlinear_arith)
                requires
                    delta_num > 0,
                    delta_num * wt_den(s) <= delta_den * wt_num(s),
                    wt_num(s) == 0,
                    wt_den(s) == 1,
                ;
        }
    }

    assert(abs_int(p) * e <= (2 * k) * (a.d() * ad));
    assert(abs_int(q) * e <= k * (b.d() * bd));
    assert(0 <= an);
    assert(an * bd <= bn * ad);

    // Expand the quotient difference into its numerator- and
    // denominator-perturbation terms.
    let aa = a.n() * ad;
    let bb = an * a.d();
    let cc = b.d() * bn;
    let dd = b.n() * bd;
    assert(p == aa - bb);
    vstd::arithmetic::mul::lemma_mul_is_commutative(b.d(), bn);
    assert(cc == bn * b.d());
    assert(q == dd - cc);
    assert(crate::q::div_n(a, b) * (ad * bn) == aa * cc) by (nonlinear_arith)
        requires
            crate::q::div_n(a, b) == a.n() * b.d(),
            aa == a.n() * ad,
            cc == b.d() * bn,
    ;
    assert((an * bd) * crate::q::div_d(a, b) == bb * dd) by (nonlinear_arith)
        requires
            crate::q::div_d(a, b) == a.d() * b.n(),
            bb == an * a.d(),
            dd == b.n() * bd,
    ;
    assert(x == aa * cc - bb * dd);
    assert(p * cc - q * bb == aa * cc - bb * dd) by (nonlinear_arith)
        requires
            p == aa - bb,
            q == dd - cc,
    ;
    assert(x == p * (b.d() * bn) - q * (an * a.d()))
        by (nonlinear_arith)
        requires
            x == aa * cc - bb * dd,
            p * cc - q * bb == aa * cc - bb * dd,
            cc == b.d() * bn,
            bb == an * a.d(),
    ;
    crate::lipschitz::lemma_abs_triangle(p * (b.d() * bn), q * (an * a.d()));
    crate::lipschitz::lemma_abs_prod(p, b.d() * bn);
    crate::lipschitz::lemma_abs_prod(q, an * a.d());
    assert(abs_int(b.d() * bn) == b.d() * bn);
    assert(abs_int(an * a.d()) == an * a.d());
    assert(abs_int(x)
        <= abs_int(p) * (b.d() * bn) + abs_int(q) * (an * a.d()));

    // Scale the two accumulator-error hypotheses by the other positive
    // factors in the quotient identity.
    assert((abs_int(p) * e) * (b.d() * bn)
        <= ((2 * k) * (a.d() * ad)) * (b.d() * bn)) by (nonlinear_arith)
        requires
            abs_int(p) * e <= (2 * k) * (a.d() * ad),
            b.d() > 0,
            bn > 0,
    ;
    assert((abs_int(q) * e) * (an * a.d())
        <= (k * (b.d() * bd)) * (an * a.d())) by (nonlinear_arith)
        requires
            abs_int(q) * e <= k * (b.d() * bd),
            an >= 0,
            a.d() > 0,
    ;
    assert((k * (b.d() * bd)) * (an * a.d())
        <= k * b.d() * bn * ad * a.d()) by (nonlinear_arith)
        requires
            an * bd <= bn * ad,
            k > 0,
            b.d() > 0,
            a.d() > 0,
    ;
    let g = k * a.d() * ad * b.d() * bn;
    assert(((2 * k) * (a.d() * ad)) * (b.d() * bn) == 2 * g)
        by (nonlinear_arith)
        requires g == k * a.d() * ad * b.d() * bn;
    assert((k * (b.d() * bd)) * (an * a.d()) <= g)
        by (nonlinear_arith)
        requires
            (k * (b.d() * bd)) * (an * a.d())
                <= k * b.d() * bn * ad * a.d(),
            g == k * a.d() * ad * b.d() * bn,
    ;
    assert(abs_int(x) * e
        <= (abs_int(p) * (b.d() * bn) + abs_int(q) * (an * a.d())) * e)
        by (nonlinear_arith)
        requires
            e > 0,
            abs_int(x)
                <= abs_int(p) * (b.d() * bn) + abs_int(q) * (an * a.d()),
    ;
    assert((abs_int(p) * (b.d() * bn) + abs_int(q) * (an * a.d())) * e
        == (abs_int(p) * e) * (b.d() * bn)
            + (abs_int(q) * e) * (an * a.d())) by (nonlinear_arith);
    assert(abs_int(x) * e <= 3 * g) by (nonlinear_arith)
        requires
            abs_int(x) * e
                <= (abs_int(p) * (b.d() * bn) + abs_int(q) * (an * a.d())) * e,
            (abs_int(p) * (b.d() * bn) + abs_int(q) * (an * a.d())) * e
                == (abs_int(p) * e) * (b.d() * bn)
                    + (abs_int(q) * e) * (an * a.d()),
            (abs_int(p) * e) * (b.d() * bn) <= 2 * g,
            (abs_int(q) * e) * (an * a.d()) <= g,
    ;
    assert(abs_int(x) * e <= 3 * k * a.d() * ad * b.d() * bn)
        by (nonlinear_arith)
        requires
            abs_int(x) * e <= 3 * g,
            g == k * a.d() * ad * b.d() * bn,
    ;

    // `b >= delta/2` turns the three error units above into six units
    // divided by delta.
    assert(delta_num * b.d() <= 2 * delta_den * b.n());
    assert(abs_int(x) * (delta_num * e)
        <= (6 * k * delta_den)
            * ((a.d() * b.n()) * (ad * bn))) by (nonlinear_arith)
        requires
            abs_int(x) * e <= 3 * k * a.d() * ad * b.d() * bn,
            delta_num * b.d() <= 2 * delta_den * b.n(),
            k > 0,
            a.d() > 0,
            ad > 0,
            bn > 0,
            delta_num > 0,
            e > 0,
    ;

    // The exact mean lies in [0,1], while the just-proved quotient error is
    // at most 3 under the half-delta hypothesis.  Therefore the unrounded
    // quotient has magnitude at most 4.  This is the magnitude needed to
    // turn the final nearest-rounding R3 bound into an absolute 2/2^61.
    let qn = crate::q::div_n(a, b);
    let qd = crate::q::div_d(a, b);
    let un = an * bd;
    let ud = ad * bn;
    assert(qd > 0) by (nonlinear_arith)
        requires
            a.d() > 0,
            b.n() > 0,
            qd == a.d() * b.n(),
    ;
    assert(ud > 0) by (nonlinear_arith)
        requires ad > 0, bn > 0, ud == ad * bn;
    assert(0 <= un && un <= ud) by (nonlinear_arith)
        requires
            an >= 0,
            bd > 0,
            an * bd <= bn * ad,
            un == an * bd,
            ud == ad * bn,
    ;
    assert(6 * k * delta_den <= 3 * delta_num * e) by (nonlinear_arith)
        requires
            2 * k * delta_den <= delta_num * e,
    ;
    assert(abs_int(x) <= 3 * qd * ud) by (nonlinear_arith)
        requires
            delta_num > 0,
            e > 0,
            qd > 0,
            ud > 0,
            abs_int(x) * (delta_num * e)
                <= (6 * k * delta_den) * (qd * ud),
            6 * k * delta_den <= 3 * delta_num * e,
    ;
    assert(qn * ud == x + un * qd) by (nonlinear_arith)
        requires
            x == qn * (ad * bn) - (an * bd) * qd,
            un == an * bd,
            ud == ad * bn,
    ;
    crate::lipschitz::lemma_abs_triangle(x, un * qd);
    crate::lipschitz::lemma_abs_prod(qn, ud);
    assert(abs_int(ud) == ud);
    assert(abs_int(un * qd) == un * qd);
    assert(abs_int(qn) * ud <= abs_int(x) + un * qd);
    assert(abs_int(qn) * ud <= 4 * qd * ud) by (nonlinear_arith)
        requires
            abs_int(qn) * ud <= abs_int(x) + un * qd,
            abs_int(x) <= 3 * qd * ud,
            un <= ud,
            qd > 0,
    ;
    assert(abs_int(qn) <= 4 * qd) by (nonlinear_arith)
        requires
            ud > 0,
            abs_int(qn) * ud <= 4 * qd * ud,
    ;
    assert(max_int(qd, abs_int(qn)) <= 4 * qd) by (nonlinear_arith)
        requires
            qd > 0,
            abs_int(qn) <= 4 * qd,
    ;
}

/// R3 plus a magnitude bound on the exact value converts to a one-step
/// absolute-error bound. This is "part (a)" of every V8 induction step
/// elsewhere in this file. It is a separate lemma because
/// `theorem_wm_num_error_accumulation` applies it twice per element instead of
/// once: once for the `mul` and once for the `add`.
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

/// V8 for `weighted_mean`'s numerator accumulator: within `2k · m · 2^-61` of
/// `Σ w_i · x_i` after `k` pairs, twice `sum`'s rate because each pair rounds
/// twice. No `all_unit` is needed: it is a sum of independently rounded
/// products. `theorem_weighted_mean_return_error` composes this with the
/// denominator bound through the division.
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
        Rat::lemma_from_raw_spec_components(0, 1);
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
        // product's own error (1 unit) across the exact addition. Errors from
        // two independent approximants add.
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

/// Returned value of `weighted_mean`: with weights and values in `[0, 1]`,
/// non-saturating prefixes, and exact weight sum at least `delta_num/delta_den`,
/// the result is within `8 · len(s) · delta_den / (delta_num · 2^61)` of the
/// exact mean. The half-delta hypothesis keeps the rounded denominator
/// positive and conditions the quotient bound.
pub proof fn theorem_weighted_mean_return_error(
    s: Seq<(Rat, Rat)>,
    delta_num: int,
    delta_den: int,
)
    requires
        all_wf_pairs(s),
        all_unit_pairs(s),
        delta_num > 0,
        delta_den > 0,
        // Exact weight sum >= delta.
        delta_num * wt_den(s) <= delta_den * wt_num(s),
        // Explicit non-saturating, unit-magnitude prefix hypotheses used by
        // the two existing accumulation inductions.
        wt_bounded(s, 1),
        wm_num_bounded(s, 1),
        // len(s)/2^61 <= delta/2.
        2 * (s.len() as int) * delta_den <= delta_num * pow2(precision_b()),
        // The final quotient must remain on the ordinary R3 path.
        !crate::round::saturated(
            crate::q::div_n(wm_num_fold_val(s), wt_fold_val(s)),
            crate::q::div_d(wm_num_fold_val(s), wt_fold_val(s)),
        ),
    ensures
        wt_fold_val(s).n() > 0,
        crate::lipschitz::frac_diff_le(
            crate::round::round_frac(
                crate::q::div_n(wm_num_fold_val(s), wt_fold_val(s)),
                crate::q::div_d(wm_num_fold_val(s), wt_fold_val(s)),
                Dir::Nearest,
            ).n(),
            crate::round::round_frac(
                crate::q::div_n(wm_num_fold_val(s), wt_fold_val(s)),
                crate::q::div_d(wm_num_fold_val(s), wt_fold_val(s)),
                Dir::Nearest,
            ).d(),
            wsum_num(s) * wt_den(s),
            wsum_den(s) * wt_num(s),
            8 * (s.len() as int) * delta_den,
            delta_num * pow2(precision_b()),
        ),
{
    lemma_wm_num_fold_wf(s);
    lemma_wt_fold_wf(s);
    theorem_wm_num_error_accumulation(s, 1);
    theorem_wm_denom_error_accumulation(s, 1);
    lemma_wm_exact_numerator_le_denominator(s);
    lemma_wm_return_bound_composition(s, delta_num, delta_den);

    let a = wm_num_fold_val(s);
    let b = wt_fold_val(s);
    let qn = crate::q::div_n(a, b);
    let qd = crate::q::div_d(a, b);
    let un = wsum_num(s) * wt_den(s);
    let ud = wsum_den(s) * wt_num(s);
    let r = crate::round::round_frac(qn, qd, Dir::Nearest);
    let k = s.len() as int;
    let e = pow2(precision_b());

    crate::q::lemma_op_widths(a, b);
    crate::round::lemma_round_frac_wf(qn, qd, Dir::Nearest);
    crate::round::lemma_r3_error_nearest(qn, qd);
    lemma_pow2_pos(precision_b());
    assert(e > 0);
    assert(pow2(precision_b_nearest()) == 2 * e);
    assert(qd > 0);
    assert(wt_num(s) > 0) by (nonlinear_arith)
        requires
            delta_num > 0,
            wt_den(s) > 0,
            delta_den > 0,
            delta_num * wt_den(s) <= delta_den * wt_num(s),
    ;
    assert(ud > 0) by (nonlinear_arith)
        requires
            wsum_den(s) > 0,
            wt_num(s) > 0,
            ud == wsum_den(s) * wt_num(s),
    ;
    assert(max_int(qd, abs_int(qn)) <= 4 * qd);

    // Nearest rounding contributes at most 4/2^62 == 2/2^61 because the
    // pre-rounding quotient has magnitude at most four.
    assert(abs_int(r.n() * qd - qn * r.d()) * (2 * e)
        <= r.d() * max_int(qd, abs_int(qn)));
    assert(abs_int(r.n() * qd - qn * r.d()) * e <= 2 * (r.d() * qd))
        by (nonlinear_arith)
        requires
            e > 0,
            abs_int(r.n() * qd - qn * r.d()) * (2 * e)
                <= r.d() * max_int(qd, abs_int(qn)),
            max_int(qd, abs_int(qn)) <= 4 * qd,
            r.d() > 0,
            qd > 0,
    ;
    assert(abs_int(r.n() * qd - qn * r.d()) * (delta_num * e)
        <= (2 * delta_num) * (r.d() * qd)) by (nonlinear_arith)
        requires
            delta_num > 0,
            abs_int(r.n() * qd - qn * r.d()) * e <= 2 * (r.d() * qd),
    ;
    assert(delta_num * e > 0) by (nonlinear_arith)
        requires delta_num > 0, e > 0;

    // Compose final rounding (2*delta_num units on the common denominator)
    // with the pre-rounding quotient perturbation (6*k*delta_den units).
    crate::lipschitz::lemma_frac_triangle(
        r.n(),
        r.d(),
        qn,
        qd,
        un,
        ud,
        2 * delta_num,
        6 * k * delta_den,
        delta_num * e,
    );

    // Unit weights give exact sum(w) <= k, while delta <= sum(w), hence
    // delta <= k.  This absorbs the two final-rounding units into the stated
    // loose constant eight.
    assert(delta_num * wt_den(s) <= delta_den * wt_num(s));
    assert(wt_num(s) <= k * wt_den(s));
    assert(delta_num <= k * delta_den) by (nonlinear_arith)
        requires
            wt_den(s) > 0,
            delta_den > 0,
            delta_num * wt_den(s) <= delta_den * wt_num(s),
            wt_num(s) <= k * wt_den(s),
    ;
    assert(2 * delta_num + 6 * k * delta_den <= 8 * k * delta_den)
        by (nonlinear_arith)
        requires
            delta_num <= k * delta_den,
    ;
    assert(abs_int(r.n() * ud - un * r.d()) * (delta_num * e)
        <= (8 * k * delta_den) * (r.d() * ud)) by (nonlinear_arith)
        requires
            abs_int(r.n() * ud - un * r.d()) * (delta_num * e)
                <= (2 * delta_num + 6 * k * delta_den) * (r.d() * ud),
            2 * delta_num + 6 * k * delta_den <= 8 * k * delta_den,
            r.d() > 0,
            ud > 0,
    ;
}

} // verus!
