// Under development (reported non-fatal). V7: Lipschitz perturbation bounds for
// the arithmetic kernels — the enabling layer for a future interval type. Stated
// with two-sided (division-free) perturbation intervals over ghost `int`.

use vstd::prelude::*;

verus! {

/// **V7 (add/sub)**: perturbing the operands of `a + b` by `±da`, `±db` perturbs
/// the sum by at most `±(da + db)` (triangle inequality). Linear — no domain bound.
pub proof fn lipschitz_add(a: int, a2: int, b: int, b2: int, da: int, db: int)
    requires
        -da <= a - a2 <= da,
        -db <= b - b2 <= db,
    ensures
        -(da + db) <= (a + b) - (a2 + b2) <= da + db,
{
}

/// **V7 (mul)**: on a domain bounded by `m` (`|a| ≤ m`, `|b'| ≤ m`), perturbing
/// the operands of `a·b` by `±da`, `±db` perturbs the product by at most
/// `±m·(da + db)`. This is the Lipschitz constant an interval-multiply needs.
pub proof fn lipschitz_mul(a: int, a2: int, b: int, b2: int, m: int, da: int, db: int)
    requires
        m >= 0, da >= 0, db >= 0,
        -m <= a <= m,
        -m <= b2 <= m,
        -da <= a - a2 <= da,
        -db <= b - b2 <= db,
    ensures
        -(m * db + m * da) <= a * b - a2 * b2 <= m * db + m * da,
{
    // a*b - a2*b2 == a*(b - b2) + b2*(a - a2)
    assert(a * b - a2 * b2 == a * (b - b2) + b2 * (a - a2)) by (nonlinear_arith);
    // |a*(b-b2)| <= m*db  and  |b2*(a-a2)| <= m*da  (bounded × bounded)
    assert(-(m * db) <= a * (b - b2) <= m * db) by (nonlinear_arith)
        requires -m <= a <= m, -db <= b - b2 <= db, m >= 0, db >= 0;
    assert(-(m * da) <= b2 * (a - a2) <= m * da) by (nonlinear_arith)
        requires -m <= b2 <= m, -da <= a - a2 <= da, m >= 0, da >= 0;
}

fn main() {}

}
