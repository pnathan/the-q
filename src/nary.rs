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
//! The accumulated error after `k` elements is `k · 2^-61 · max(1, |exact|)`
//! (theorem `theorem_sum_error_accumulation`).
//!
//! **All three helpers carry the determinism-pinning equality, not just
//! `sum`.** `sum` `ensures r == fold_val(xs@)`: the result is pinned to a
//! spec *function* of the input, not merely to a set of properties, and that
//! is what makes `add(a, b) == add(b, a)` provably feed the same integers into
//! the same fold and what makes V8-style accumulation reasoning available.
//! `product` and `weighted_mean` now carry the equivalent (`prod_fold_val`,
//! `wm_fold_val`) — the architectural point applies uniformly across the
//! n-ary layer instead of stopping at `sum`.

use verus_builtin_macros::verus;

#[allow(unused_imports)]
use verus_builtin::*;
#[allow(unused_imports)]
use vstd::prelude::*;

#[allow(unused_imports)]
use crate::model::*;
#[allow(unused_imports)]
use crate::types::{Dir, Q};

verus! {

// ---------------------------------------------------------------------------
// The exact value of a fold, in ghost form
// ---------------------------------------------------------------------------

/// Numerator of the exact left-fold sum of `s`.
pub open spec fn sum_num(s: Seq<Q>) -> int
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
pub open spec fn sum_den(s: Seq<Q>) -> int
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
pub open spec fn prod_num(s: Seq<Q>) -> int
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
pub open spec fn prod_den(s: Seq<Q>) -> int
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
pub open spec fn all_wf(s: Seq<Q>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> (#[trigger] s[i]).wf()
}

// ---------------------------------------------------------------------------
// The helpers
// ---------------------------------------------------------------------------

/// `xs[0] + xs[1] + ... `, left to right. Empty slice gives `0`.
pub fn sum(xs: &[Q]) -> (r: Q)
    requires
        all_wf(xs@),
    ensures
        r.wf(),
        // The fold is a *function* of the input, in a fixed order. This equality
        // is what makes the result reproducible, and it is what carries the V8
        // bound (`theorem_sum_error_accumulation`) over to the real code.
        r == fold_val(xs@),
{
    let mut acc = Q::zero();
    let mut i: usize = 0;
    proof {
        assert(xs@.subrange(0, 0) =~= Seq::<Q>::empty());
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
        acc = Q::add(acc, xs[i]);
        i = i + 1;
    }
    proof {
        assert(xs@.subrange(0, xs.len() as int) =~= xs@);
    }
    acc
}

/// Extending a prefix by one element extends the fold by one step.
pub proof fn lemma_fold_snoc(s: Seq<Q>, i: int)
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
pub fn product(xs: &[Q]) -> (r: Q)
    requires
        all_wf(xs@),
    ensures
        r.wf(),
        // Pinned to a spec *function* of the input, exactly as `sum` is
        // pinned to `fold_val` — this is what makes `product` reproducible
        // and available to V8-style reasoning, not just "some value
        // satisfying the invariant".
        r == prod_fold_val(xs@),
{
    let mut acc = Q::one();
    let mut i: usize = 0;
    proof {
        assert(xs@.subrange(0, 0) =~= Seq::<Q>::empty());
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
        acc = Q::mul(acc, xs[i]);
        i = i + 1;
    }
    proof {
        assert(xs@.subrange(0, xs.len() as int) =~= xs@);
    }
    acc
}

/// The value the left fold of `s` under `mul` produces, as a *function* — the
/// `product` analogue of [`fold_val`].
pub open spec fn prod_fold_val(s: Seq<Q>) -> Q
    decreases s.len(),
{
    if s.len() == 0 {
        Q { num: 1, den: 1 }
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

/// Extending a prefix by one element extends the product fold by one step.
pub proof fn lemma_prod_fold_snoc(s: Seq<Q>, i: int)
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
pub open spec fn all_wf_pairs(s: Seq<(Q, Q)>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> (#[trigger] s[i]).0.wf() && s[i].1.wf()
}

/// The running weighted-sum numerator `weighted_mean` accumulates, as a
/// *function* of the processed prefix.
pub open spec fn wm_acc_num(pairs: Seq<(Q, Q)>) -> Q
    decreases pairs.len(),
{
    if pairs.len() == 0 {
        Q { num: 0, den: 1 }
    } else {
        let init = pairs.subrange(0, pairs.len() as int - 1);
        let last = pairs[pairs.len() as int - 1];
        let prev = wm_acc_num(init);
        let prod = crate::round::round_frac(
            crate::q::mul_n(last.0, last.1),
            crate::q::prod_d(last.0, last.1),
            Dir::Nearest,
        );
        crate::round::round_frac(
            crate::q::add_n(prev, prod),
            crate::q::prod_d(prev, prod),
            Dir::Nearest,
        )
    }
}

/// The running weight sum `weighted_mean` accumulates, as a *function* of the
/// processed prefix.
pub open spec fn wm_acc_den(pairs: Seq<(Q, Q)>) -> Q
    decreases pairs.len(),
{
    if pairs.len() == 0 {
        Q { num: 0, den: 1 }
    } else {
        let init = pairs.subrange(0, pairs.len() as int - 1);
        let last = pairs[pairs.len() as int - 1];
        let prev = wm_acc_den(init);
        crate::round::round_frac(
            crate::q::add_n(prev, last.0),
            crate::q::prod_d(prev, last.0),
            Dir::Nearest,
        )
    }
}

/// The value `weighted_mean` produces, as a *function* of the whole input —
/// the same determinism-pinning shape `fold_val` gives `sum`.
pub open spec fn wm_fold_val(pairs: Seq<(Q, Q)>) -> Option<Q> {
    let num = wm_acc_num(pairs);
    let den = wm_acc_den(pairs);
    if den.n() == 0 {
        None
    } else {
        Some(
            crate::round::round_frac(
                crate::q::div_n(num, den),
                crate::q::div_d(num, den),
                Dir::Nearest,
            ),
        )
    }
}

/// Extending a prefix by one pair extends both running accumulators by one
/// step.
pub proof fn lemma_wm_acc_snoc(pairs: Seq<(Q, Q)>, i: int)
    requires
        0 <= i < pairs.len(),
    ensures
        ({
            let prev_num = wm_acc_num(pairs.subrange(0, i));
            let prod = crate::round::round_frac(
                crate::q::mul_n(pairs[i].0, pairs[i].1),
                crate::q::prod_d(pairs[i].0, pairs[i].1),
                Dir::Nearest,
            );
            wm_acc_num(pairs.subrange(0, i + 1)) == crate::round::round_frac(
                crate::q::add_n(prev_num, prod),
                crate::q::prod_d(prev_num, prod),
                Dir::Nearest,
            )
        }),
        ({
            let prev_den = wm_acc_den(pairs.subrange(0, i));
            wm_acc_den(pairs.subrange(0, i + 1)) == crate::round::round_frac(
                crate::q::add_n(prev_den, pairs[i].0),
                crate::q::prod_d(prev_den, pairs[i].0),
                Dir::Nearest,
            )
        }),
{
    let pre = pairs.subrange(0, i + 1);
    assert(pre.len() == i + 1);
    assert(pre[pre.len() as int - 1] == pairs[i]);
    assert(pre.subrange(0, pre.len() as int - 1) =~= pairs.subrange(0, i));
}

/// `sum(w_i · x_i) / sum(w_i)` — the shape the averaging-belief-fusion formula
/// needs.
///
/// `None` when the weights sum to zero (the mean is undefined there, and this
/// crate does not invent a value for it).
pub fn weighted_mean(pairs: &[(Q, Q)]) -> (r: Option<Q>)
    requires
        all_wf_pairs(pairs@),
    ensures
        r.is_some() ==> r.unwrap().wf(),
        // Pinned to a spec function of the input, the same way `sum` is
        // pinned to `fold_val` — see `wm_fold_val`.
        r == wm_fold_val(pairs@),
{
    let mut acc_num = Q::zero();
    let mut acc_w = Q::zero();
    let mut i: usize = 0;
    proof {
        assert(pairs@.subrange(0, 0) =~= Seq::<(Q, Q)>::empty());
    }
    while i < pairs.len()
        invariant
            acc_num.wf(),
            acc_w.wf(),
            all_wf_pairs(pairs@),
            i <= pairs.len(),
            acc_num == wm_acc_num(pairs@.subrange(0, i as int)),
            acc_w == wm_acc_den(pairs@.subrange(0, i as int)),
        decreases pairs.len() - i,
    {
        proof {
            lemma_wm_acc_snoc(pairs@, i as int);
        }
        let (w, x) = pairs[i];
        acc_num = Q::add(acc_num, Q::mul(w, x));
        acc_w = Q::add(acc_w, w);
        i = i + 1;
    }
    proof {
        assert(pairs@.subrange(0, pairs.len() as int) =~= pairs@);
    }
    if acc_w.is_zero() {
        None
    } else {
        Some(Q::div(acc_num, acc_w))
    }
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
pub open spec fn fold_val(s: Seq<Q>) -> Q
    decreases s.len(),
{
    if s.len() == 0 {
        Q { num: 0, den: 1 }
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

/// Every prefix of the fold has step values bounded by `m`, and stays on a
/// non-saturating path. This is the hypothesis V8 needs and cannot invent:
/// without a magnitude bound on the intermediates there is nothing for the
/// accumulated error to be measured against.
///
/// For this crate's actual domain it is trivially satisfiable — opinions live
/// in `[0, 1]`, so `m == 1`.
pub open spec fn fold_bounded(s: Seq<Q>, m: int) -> bool
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
pub proof fn lemma_fold_wf(s: Seq<Q>)
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
pub proof fn theorem_sum_error_accumulation(s: Seq<Q>, m: int)
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
pub proof fn theorem_exact_fold_is_exact(s: Seq<Q>)
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
pub open spec fn fold_exact(s: Seq<Q>) -> bool
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
/// Explicit `rlimit`: this proof already sat close enough to the default
/// budget that unrelated additions elsewhere in this module (adding the
/// `product`/`weighted_mean` determinism-pinning equalities) pushed one of its
/// nonlinear steps over — the same fragility `saturation.rs`'s header
/// documents for `model.rs`/`laws.rs`. Fixing the budget here decouples this
/// proof from future context growth instead of re-tuning it again next time.
#[verifier::rlimit(40)]
pub proof fn lemma_exact_step(prev: Q, last: Q, r: Q, pn: int, pd: int, tn: int, td: int)
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

} // verus!
