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
//! The accumulated error after `k` elements is `k · 2^-60 · max(1, |exact|)`
//! (theorem `theorem_sum_error_accumulation`).

use verus_builtin_macros::verus;

#[allow(unused_imports)]
use verus_builtin::*;
#[allow(unused_imports)]
use vstd::prelude::*;

#[allow(unused_imports)]
use crate::model::*;
use crate::types::Q;

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
{
    let mut acc = Q::zero();
    let mut i: usize = 0;
    while i < xs.len()
        invariant
            acc.wf(),
            all_wf(xs@),
            i <= xs.len(),
        decreases xs.len() - i,
    {
        acc = Q::add(acc, xs[i]);
        i = i + 1;
    }
    acc
}

/// `xs[0] * xs[1] * ... `, left to right. Empty slice gives `1`.
pub fn product(xs: &[Q]) -> (r: Q)
    requires
        all_wf(xs@),
    ensures
        r.wf(),
{
    let mut acc = Q::one();
    let mut i: usize = 0;
    while i < xs.len()
        invariant
            acc.wf(),
            all_wf(xs@),
            i <= xs.len(),
        decreases xs.len() - i,
    {
        acc = Q::mul(acc, xs[i]);
        i = i + 1;
    }
    acc
}

/// Every element of a slice of `(weight, value)` pairs is well-formed.
pub open spec fn all_wf_pairs(s: Seq<(Q, Q)>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> (#[trigger] s[i]).0.wf() && s[i].1.wf()
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
{
    let mut acc_num = Q::zero();
    let mut acc_w = Q::zero();
    let mut i: usize = 0;
    while i < pairs.len()
        invariant
            acc_num.wf(),
            acc_w.wf(),
            all_wf_pairs(pairs@),
            i <= pairs.len(),
        decreases pairs.len() - i,
    {
        let (w, x) = pairs[i];
        acc_num = Q::add(acc_num, Q::mul(w, x));
        acc_w = Q::add(acc_w, w);
        i = i + 1;
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

/// **V8.** After `k` folded elements the accumulated error against the exact
/// fold is at most `k · 2^-60 · max(1, |exact|)`.
///
/// The induction is: each `add` contributes at most one fresh `2^-60` relative
/// error (R3) and the previously accumulated error is carried through addition
/// with Lipschitz constant `1` ([`crate::lipschitz::lemma_add_lipschitz`]), so
/// the bound is additive in the number of operations. Nothing here is
/// asymptotic hand-waving: for the consuming engine's worst case of ~2·10^4
/// sequential operations this is `2·10^4 · 2^-60 ≈ 2^-45.7 ≈ 2·10^-14`
/// relative — the same precision class as `f64` accumulation, but
/// deterministic and proven rather than assumed.
pub proof fn theorem_sum_error_accumulation(s: Seq<Q>, r: Q, k: nat)
    requires
        all_wf(s),
        r.wf(),
        s.len() == k,
        sum_den(s) > 0,
        // `r` is what the left fold produced.
        fold_result_of(s, r),
    ensures
        within_error_bound_k(r, sum_num(s), sum_den(s), k),
    decreases s.len(),
{
    if s.len() == 0 {
        assert(sum_num(s) == 0 && sum_den(s) == 1);
    } else {
        let init = s.subrange(0, s.len() as int - 1);
        assert(all_wf(init));
        // The inductive step: the fold over `init` is within (k-1) units, the
        // final `add` contributes at most one more (R3), and addition carries
        // the earlier error with constant 1 (V7).
        let prev = choose|p: Q| fold_result_of(init, p);
        crate::lipschitz::lemma_error_accumulates_additively(
            prev,
            sum_num(init),
            sum_den(init),
            s[s.len() as int - 1],
            r,
            (k - 1) as nat,
        );
    }
}

/// `r` is the value the left fold of `s` produces. Defined by recursion so the
/// accumulation theorem has something to induct on.
pub open spec fn fold_result_of(s: Seq<Q>, r: Q) -> bool
    decreases s.len(),
{
    if s.len() == 0 {
        r.n() == 0 && r.d() == 1
    } else {
        exists|prev: Q|
            #[trigger] fold_result_of(s.subrange(0, s.len() as int - 1), prev) && r
                == crate::round::round_frac(
                crate::q::add_n(prev, s[s.len() as int - 1]),
                crate::q::prod_d(prev, s[s.len() as int - 1]),
                crate::types::Dir::Nearest,
            )
    }
}

/// The exact-path corollary for folds: if no element of the fold ever leaves
/// the budget, the whole fold is exact.
pub proof fn theorem_exact_fold_is_exact(s: Seq<Q>, r: Q)
    requires
        all_wf(s),
        r.wf(),
        fold_result_of(s, r),
        sum_den(s) > 0,
        forall|i: int| 0 <= i <= s.len() ==> #[trigger] fold_prefix_exact(s, i),
    ensures
        q_is(r, sum_num(s), sum_den(s)),
    decreases s.len(),
{
    if s.len() == 0 {
    } else {
        let init = s.subrange(0, s.len() as int - 1);
        theorem_exact_fold_is_exact(init, choose|prev: Q| fold_result_of(init, prev));
    }
}

/// The `i`-th prefix of the fold stays on the exact path.
pub open spec fn fold_prefix_exact(s: Seq<Q>, i: int) -> bool {
    0 <= i <= s.len() ==> crate::round::exact_path(
        sum_num(s.subrange(0, i)),
        sum_den(s.subrange(0, i)),
    )
}

} // verus!
