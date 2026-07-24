// Machine-checked obligations (admit-free) — a CI hard-gate target.
//
// Self-contained (own crate root + `fn main`), verified by `verus`. Uses only
// integer reasoning and `nonlinear_arith`; no bit-shifts on ghost `int`, no
// `admit`. Covers, for the comparison path and sign laws:
//   V2 — no i128 overflow: budget-bounded cross-products fit i128.
//   V3 — value correctness: the exec i128 comparison equals the ghost order.
//   V6 — negation is an involution and preserves the bound.
//
// Run: `verus verus/src/verified.rs`

use vstd::prelude::*;

verus! {

/// `2^62 - 1`, the width budget (I2), as a concrete literal so proofs need no
/// `pow2` machinery.
pub open spec fn budget() -> int { 4611686018427387903 }

/// `i128::MAX == 2^127 - 1`, as a literal for overflow bounds.
pub open spec fn i128_max() -> int { 170141183460469231731687303715884105727 }

/// The mirror of the executable `Q { num: i64, den: i64 }`.
pub struct Q {
    pub num: i64,
    pub den: i64,
}

pub open spec fn abs_int(x: int) -> int { if x < 0 { -x } else { x } }

/// I2 (bounded) together with `den > 0` — the part of the invariant the
/// comparison/sign proofs depend on.
pub open spec fn bounded(q: Q) -> bool {
    &&& q.den >= 1
    &&& -budget() <= q.num as int <= budget()
    &&& q.den as int <= budget()
}

/// Ghost order, division-free (valid because both denominators are positive).
pub open spec fn q_lt(a: Q, b: Q) -> bool {
    (a.num as int) * (b.den as int) < (b.num as int) * (a.den as int)
}

pub open spec fn q_le(a: Q, b: Q) -> bool {
    (a.num as int) * (b.den as int) <= (b.num as int) * (a.den as int)
}

/// V2 core: the product of two budget-bounded integers lies within `±budget^2`,
/// which is far inside `i128`. Proven by `nonlinear_arith`.
pub proof fn lemma_prod_bound(x: int, y: int)
    requires
        -budget() <= x <= budget(),
        -budget() <= y <= budget(),
    ensures
        -(budget() * budget()) <= x * y <= budget() * budget(),
        budget() * budget() < i128_max(),
{
    assert(-(budget() * budget()) <= x * y <= budget() * budget()) by (nonlinear_arith)
        requires
            -budget() <= x <= budget(),
            -budget() <= y <= budget();
    // budget^2 = 2^124 - 2^63 + 1 < 2^127 - 1 = i128::MAX  (constant fact).
    assert(budget() * budget() < i128_max());
}

/// V2 + V3 for comparison: the exec i128 cross-multiplication never overflows
/// (V2) and its result equals the ghost order `q_lt` (V3).
pub fn q_lt_exec(a: Q, b: Q) -> (r: bool)
    requires bounded(a), bounded(b),
    ensures r == q_lt(a, b),
{
    proof {
        lemma_prod_bound(a.num as int, b.den as int);
        lemma_prod_bound(b.num as int, a.den as int);
    }
    let lhs: i128 = (a.num as i128) * (b.den as i128);
    let rhs: i128 = (b.num as i128) * (a.den as i128);
    lhs < rhs
}

/// V6: negation is an involution and preserves the bound (I2 is symmetric in
/// sign; `|num| <= 2^62 - 1` excludes `i64::MIN`, so `-num` cannot overflow).
pub fn neg(q: Q) -> (r: Q)
    requires bounded(q),
    ensures
        bounded(r),
        r.num == -(q.num as int),
        r.den == q.den,
{
    Q { num: -q.num, den: q.den }
}

/// `-(-q) == q` exactly (double negation), as a value-level law.
pub proof fn lemma_neg_involution(q: Q)
    requires bounded(q),
    ensures -(-(q.num as int)) == q.num as int,
{
}

fn main() {}

}
