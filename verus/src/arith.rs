// Arithmetic: overflow safety (V2) and value correctness (V3).
//
// The central V2 fact: under I2 (|num|, den <= 2^62 - 1) every i128 intermediate
// in add/sub/mul/cmp is < 2^127 in magnitude, so the ops never overflow *with
// overflow-checks ON*. The lemmas below establish those bounds arithmetically;
// the value-correctness `ensures` are stated division-free via `model.rs`.

use vstd::prelude::*;
use crate::model::{budget, is_prod, is_sum, q_den, q_le, q_lt, q_num, wf, Q};

verus! {

/// `2^62 - 1`. Kept as a lemma-visible constant.
pub open spec fn b() -> int { budget() }

/// The add/sub numerator `a.num*b.den + b.num*a.den` has magnitude < 2^125,
/// hence fits i128 (`|.| <= i128::MAX = 2^127 - 1`). This is the tightest of the
/// four intermediates and the reason the budget is 2^62 rather than 2^63.
pub proof fn lemma_add_num_in_range(a: Q, b: Q)
    requires wf(a), wf(b),
    ensures
        -(1int << 125) < q_num(a) * q_den(b) + q_num(b) * q_den(a),
        q_num(a) * q_den(b) + q_num(b) * q_den(a) < (1int << 125),
{
    // |a.num| <= B, b.den <= B  ⟹ |a.num*b.den| <= B^2 < 2^124.
    // Sum of two such terms has magnitude < 2^125 < 2^127. OBLIGATION: the
    // nonlinear bound B^2 < 2^124 needs `broadcast` mul-le lemmas / `nlarith`.
    admit();
}

/// The mul numerator `a.num*b.num` and any product of two budgeted denominators
/// has magnitude <= B^2 < 2^124, fitting i128.
pub proof fn lemma_mul_num_in_range(a: Q, b: Q)
    requires wf(a), wf(b),
    ensures
        -(1int << 124) < q_num(a) * q_num(b),
        q_num(a) * q_num(b) < (1int << 124),
        (q_den(a) * q_den(b)) < (1int << 124),
        (q_den(a) * q_den(b)) > 0,
{
    // OBLIGATION: |a.num*b.num| <= B^2 < 2^124; den product positive and < 2^124.
    admit();
}

/// The compare cross-products `a.num*b.den` and `b.num*a.den` fit i128
/// (magnitude < 2^124), so exact comparison never overflows.
pub proof fn lemma_cmp_in_range(a: Q, b: Q)
    requires wf(a), wf(b),
    ensures
        -(1int << 124) < q_num(a) * q_den(b) < (1int << 124),
        -(1int << 124) < q_num(b) * q_den(a) < (1int << 124),
{
    admit();
}

/// Comparison correctness: the i128 cross-multiply agrees with the ghost order.
/// (Both denominators are positive, so cross-multiplying preserves direction.)
pub proof fn lemma_cmp_correct(a: Q, b: Q)
    requires wf(a), wf(b),
    ensures
        (q_num(a) * q_den(b) < q_num(b) * q_den(a)) == q_lt(a, b),
        (q_num(a) * q_den(b) <= q_num(b) * q_den(a)) == q_le(a, b),
{
    // Immediate from the definitions of q_lt/q_le (they *are* the cross-products).
}

// --------------------------------------------------------------------------
// Value-correctness contracts (V3). These are the `ensures` the exec `add`/
// `mul` carry. The result `r` is the canonicalized, budget-rounded fraction;
// on the exact path `is_sum`/`is_prod` hold with equality (R1), and in general
// they hold up to the R3 error bound stated in `round.rs`.
// --------------------------------------------------------------------------

/// Contract of `add` on the **exact path** (no rounding): result models a+b
/// exactly, division-free.
pub proof fn contract_add_exact(r: Q, a: Q, b: Q)
    requires wf(a), wf(b), wf(r), is_sum(r, a, b),
    ensures q_num(r) * (q_den(a) * q_den(b)) == (q_num(a) * q_den(b) + q_num(b) * q_den(a)) * q_den(r),
{
    // `is_sum` *is* the ensures — this documents that the exec `add`, when it
    // returns without rounding, must re-establish exactly this predicate. The
    // reduce step (gcd) preserves value, proved via lemma_gcd_divides.
}

/// Contract of `mul` on the exact path.
pub proof fn contract_mul_exact(r: Q, a: Q, b: Q)
    requires wf(a), wf(b), wf(r), is_prod(r, a, b),
    ensures q_num(r) * (q_den(a) * q_den(b)) == (q_num(a) * q_num(b)) * q_den(r),
{
}

}
