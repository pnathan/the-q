// Under development (reported non-fatal). V4 R4: the dyadic floor-snap is
// monotone on a fixed grid — `x <= y ⟹ round(x) <= round(y)` — needed so the
// engine's clamp/order logic survives rounding.

use vstd::prelude::*;
use vstd::arithmetic::div_mod::lemma_div_is_ordered;

verus! {

pub open spec fn pow2(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 } else { 2 * pow2((n - 1) as nat) }
}

pub proof fn pow2_pos(n: nat)
    ensures pow2(n) >= 1,
    decreases n
{
    if n == 0 {
    } else {
        pow2_pos((n - 1) as nat);
    }
}

/// **R4 (monotone)**: for two values sharing denominator `d` on the grid `1/2^s`,
/// `n1 ≤ n2` implies the floor-snap numerators are ordered — so snapping never
/// inverts the order of two comparable values.
pub proof fn snap_floor_monotone(n1: int, n2: int, d: int, s: nat)
    requires d >= 1, n1 <= n2,
    ensures (n1 * (pow2(s) as int)) / d <= (n2 * (pow2(s) as int)) / d,
{
    pow2_pos(s);
    let p = pow2(s) as int;
    assert(n1 * p <= n2 * p) by (nonlinear_arith) requires n1 <= n2, p >= 1;
    lemma_div_is_ordered(n1 * p, n2 * p, d);
}

fn main() {}

}
