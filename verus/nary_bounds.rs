// V8: n-ary helper error bounds -- after `k` left-to-right fold steps,
// each individually rounded with error `<= B`, the accumulated error is
// `<= k*B`. Spec: "ensures-clause gives the accumulated error bound
// `k·2^-B` after `k` elements" (§2.5), matching `sum`/`product`/
// `weighted_mean`'s binary-fold implementation in src/nary.rs.
//
// This is proved *generically* over an abstract per-step rounding
// function satisfying a uniform error bound, rather than tied to the
// concrete `round_to_budget` algorithm -- R3 (the concrete `2^-60` bound
// `round_to_budget` actually satisfies) isn't proved in full generality
// yet (see TRUSTED.md), so this lemma is the reusable "if each step is
// within B, the fold is within k*B" argument that V8 needs once R3 lands;
// composing it with a proved R3 is future work, not done here.
//
// Standalone Verus proof file. Checked directly via
// `verus verus/nary_bounds.rs`; see verus/smoke_test.rs's header comment
// for why these live outside the cargo package.
//
// Authored and iterated on entirely via CI feedback -- no local Verus
// available (see TRUSTED.md).

use vstd::prelude::*;

verus! {

pub open spec fn iabs(x: int) -> int {
    if x < 0 {
        -x
    } else {
        x
    }
}

/// The exact (unrounded) running sum after `k` terms: `T_0 = 0`,
/// `T_i = T_{i-1} + terms[i-1]`.
pub open spec fn exact_sum(terms: Seq<int>, k: nat) -> int
    decreases k,
{
    if k == 0 {
        0
    } else {
        exact_sum(terms, (k - 1) as nat) + terms[k as int - 1]
    }
}

/// The rounded running sum: `C_0 = 0`, `C_i = round(C_{i-1} + terms[i-1])`,
/// for an abstract per-step rounding function `round` satisfying a uniform
/// error bound `B` (`|round(y) - y| <= B` for all `y`) -- this is exactly
/// what R3 would give for `round_to_budget` restricted to the "bounded
/// magnitude <= 1" regime the spec's own error-bound statement uses
/// (`max(1, |exact|)`); the general (unbounded-magnitude) case scales `B`
/// by `|y|`, which this lemma doesn't attempt (see file header).
pub open spec fn rounded_sum(terms: Seq<int>, k: nat, round: spec_fn(int) -> int) -> int
    decreases k,
{
    if k == 0 {
        0
    } else {
        round(rounded_sum(terms, (k - 1) as nat, round) + terms[k as int - 1])
    }
}

/// V8: after `k` terms, `|rounded_sum - exact_sum| <= k * B`.
proof fn lemma_fold_error_bound(terms: Seq<int>, k: nat, round: spec_fn(int) -> int, b: int)
    requires
        b >= 0,
        terms.len() >= k,
        forall|y: int| iabs(#[trigger] round(y) - y) <= b,
    ensures
        iabs(rounded_sum(terms, k, round) - exact_sum(terms, k)) <= k * b,
    decreases k,
{
    if k == 0 {
        assert(rounded_sum(terms, k, round) == 0);
        assert(exact_sum(terms, k) == 0);
    } else {
        let km1 = (k - 1) as nat;
        lemma_fold_error_bound(terms, km1, round, b);
        let prev_rounded = rounded_sum(terms, km1, round);
        let prev_exact = exact_sum(terms, km1);
        let term = terms[k as int - 1];
        // C_k = round(C_{k-1} + term), T_k = T_{k-1} + term.
        let y = prev_rounded + term;
        assert(rounded_sum(terms, k, round) == round(y));
        assert(exact_sum(terms, k) == prev_exact + term);
        assert(iabs(round(y) - y) <= b);
        assert(iabs(prev_rounded - prev_exact) <= km1 * b);

        // Unfold both absolute-value facts into two-sided linear bounds
        // (iabs is `open`, so the solver can unfold its if/else on its
        // own), then combine additively -- pure linear arithmetic, no
        // nonlinear_arith needed for the triangle-inequality step itself.
        assert(-b <= round(y) - y && round(y) - y <= b);
        assert(-(km1 * b) <= prev_rounded - prev_exact && prev_rounded - prev_exact <= km1 * b);
        assert(round(y) - (prev_exact + term) == (round(y) - y) + (prev_rounded - prev_exact));
        assert(-(b + km1 * b) <= round(y) - (prev_exact + term));
        assert(round(y) - (prev_exact + term) <= b + km1 * b);
        assert(iabs(round(y) - (prev_exact + term)) <= b + km1 * b);
        assert(b + km1 * b == k * b) by (nonlinear_arith)
            requires
                k == km1 + 1,
        {}
    }
}

fn main() {}

} // verus!
