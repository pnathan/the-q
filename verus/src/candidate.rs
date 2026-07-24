// Under development (reported non-fatal). V8: n-ary accumulation bound — a
// left-to-right fold of k operations, each within `eps` of exact, accumulates
// to within `k·eps`. Abstract triangle-inequality induction over the per-step
// error sequence.

use vstd::prelude::*;

verus! {

/// Sum of an integer sequence.
pub open spec fn seq_sum(s: Seq<int>) -> int
    decreases s.len()
{
    if s.len() == 0 { 0 } else { s[0] + seq_sum(s.subrange(1, s.len() as int)) }
}

/// **V8**: if each of `k = s.len()` per-step errors is within `±eps`, their
/// accumulation is within `±k·eps`.
pub proof fn accumulation_bound(s: Seq<int>, eps: int)
    requires
        eps >= 0,
        forall|i: int| 0 <= i < s.len() ==> -eps <= #[trigger] s[i] <= eps,
    ensures
        -((s.len() as int) * eps) <= seq_sum(s) <= (s.len() as int) * eps,
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        let rest = s.subrange(1, s.len() as int);
        assert(rest.len() == s.len() - 1);
        assert(forall|i: int| 0 <= i < rest.len() ==> -eps <= #[trigger] rest[i] <= eps) by {
            assert(forall|i: int| 0 <= i < rest.len() ==> rest[i] == s[i + 1]);
        };
        accumulation_bound(rest, eps);
        assert(seq_sum(s) == s[0] + seq_sum(rest));
        assert(-((s.len() as int) * eps) <= seq_sum(s) <= (s.len() as int) * eps)
            by (nonlinear_arith)
            requires
                eps >= 0,
                -eps <= s[0] <= eps,
                -((rest.len() as int) * eps) <= seq_sum(rest) <= (rest.len() as int) * eps,
                rest.len() == s.len() - 1,
                seq_sum(s) == s[0] + seq_sum(rest);
    }
}

fn main() {}

}
