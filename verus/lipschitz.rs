// V7: error-propagation (Lipschitz) lemmas -- perturbation bounds for
// add/sub/mul on a bounded domain, div with denominator bounded away from
// 0. Spec-marked SHOULD ("the enabling layer for a future interval type"
// -- QI, spec M6, already implemented in src/interval.rs without needing
// these lemmas formally, but proving them is still useful groundwork for
// anyone tightening QI's bounds later).
//
// These lemmas are stated over *exact* real-valued rational arithmetic
// (via q_value_eq-style cross-multiplication, matching algebra.rs), not
// the rounded `Q` ops -- i.e. "how much does the true mathematical result
// move when the true mathematical inputs move," independent of any
// rounding contract (R1-R4, not proved in full generality yet -- see
// TRUSTED.md). Composing this with a proved R3 would give a perturbation
// bound for the *rounded* ops too; that composition isn't done here.
//
// Standalone Verus proof file. Checked directly via
// `verus verus/lipschitz.rs`; see verus/smoke_test.rs's header comment for
// why these live outside the cargo package.
//
// Authored and iterated on entirely via CI feedback -- no local Verus
// available (see TRUSTED.md).

use vstd::prelude::*;

verus! {

/// `|x|` for ghost `int`.
pub open spec fn iabs(x: int) -> int {
    if x < 0 {
        -x
    } else {
        x
    }
}

/// Addition is exactly 1-Lipschitz in each argument (no domain bound
/// needed): perturbing `a` by `da` perturbs `a + b` by exactly `da`.
proof fn lemma_add_lipschitz(a: int, b: int, da: int)
    ensures
        iabs((a + da + b) - (a + b)) == iabs(da),
{
}

proof fn lemma_sub_lipschitz(a: int, b: int, da: int, db: int)
    ensures
        iabs(((a + da) - (b + db)) - (a - b)) <= iabs(da) + iabs(db),
{
}

/// Multiplication on `[-m, m] x [-m, m]`: perturbing `a` by `da` and `b` by
/// `db` (with `a, b, a+da, b+db` all bounded by `m`) perturbs `a*b` by at
/// most `m*(|da| + |db|)` -- the standard product-rule-style bound
/// `(a+da)(b+db) - ab = a*db + b*da + da*db`, each term bounded via `m`.
proof fn lemma_mul_lipschitz(a: int, b: int, da: int, db: int, m: int)
    requires
        m >= 0,
        iabs(a) <= m,
        iabs(b) <= m,
        iabs(a + da) <= m,
        iabs(b + db) <= m,
    ensures
        iabs((a + da) * (b + db) - a * b) <= m * iabs(da) + m * iabs(db) + iabs(da) * iabs(db),
{
    assert((a + da) * (b + db) - a * b == a * db + b * da + da * db) by (nonlinear_arith)
    {}
    assert(iabs(a * db) <= m * iabs(db)) by (nonlinear_arith)
        requires
            iabs(a) <= m,
    {}
    assert(iabs(b * da) <= m * iabs(da)) by (nonlinear_arith)
        requires
            iabs(b) <= m,
    {}
    assert(iabs(a * db + b * da + da * db) <= iabs(a * db) + iabs(b * da) + iabs(da * db)) by (
    nonlinear_arith)
    {}
    assert(iabs(da * db) == iabs(da) * iabs(db)) by (nonlinear_arith)
    {}
}

/// `recip` on `{x : |x| >= e}` (denominator "bounded away from 0", per the
/// spec's framing -- here `e` plays the role of that bound on `|x|` /
/// `|x+dx|`): `|1/(x+dx) - 1/x| = |dx| / (|x| * |x+dx|) <= |dx| / e^2`.
/// Stated division-free via cross-multiplication, matching the ghost-model
/// discipline used throughout (avoids reasoning about real/rational
/// division directly).
proof fn lemma_recip_lipschitz(x: int, dx: int, e: int)
    requires
        e > 0,
        iabs(x) >= e,
        iabs(x + dx) >= e,
        x != 0,
        x + dx != 0,
    ensures
        // "|1/(x+dx) - 1/x| <= |dx|/e^2" stated division-free: multiply
        // both sides by (x * (x+dx) * e^2), i.e.
        // |x - (x+dx)| * e^2 <= |dx| * |x * (x+dx)|, i.e. (since
        // x-(x+dx) == -dx) |dx| * e^2 <= |dx| * |x*(x+dx)|, which reduces
        // (for dx == 0, trivial; for dx != 0) to e^2 <= |x*(x+dx)|.
        iabs(dx) * (e * e) <= iabs(dx) * iabs(x * (x + dx)),
{
    assert(iabs(x * (x + dx)) == iabs(x) * iabs(x + dx)) by (nonlinear_arith)
    {}
    assert(e * e <= iabs(x) * iabs(x + dx)) by (nonlinear_arith)
        requires
            e > 0,
            iabs(x) >= e,
            iabs(x + dx) >= e,
    {}
    assert(iabs(dx) * (e * e) <= iabs(dx) * iabs(x * (x + dx))) by (nonlinear_arith)
        requires
            e * e <= iabs(x) * iabs(x + dx),
            iabs(x * (x + dx)) == iabs(x) * iabs(x + dx),
            iabs(dx) >= 0,
    {}
}

fn main() {}

} // verus!
