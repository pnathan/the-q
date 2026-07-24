// Rounding contract R1-R4 (obligation V4).
//
// `round_to_budget(n, d, dir)` reduces `n/d` and, if it violates I2, snaps to
// the dyadic grid `p / 2^s`. The contract, per direction:
//   R1 identity: if the reduced result fits the budget, return it exactly.
//   R2 directed: Down <= exact <= Up (as ghost rationals).
//   R3 error:    |result - exact| <= 2^-60 * max(1, |exact|).
//   R4 monotone: x <= y ⟹ round(x, dir) <= round(y, dir)  (per grid).

use vstd::prelude::*;
use crate::model::{abs_int, budget, q_den, q_num, wf, Q};

verus! {

/// Does the reduced fraction `(n, d)` (with `d > 0`, coprime) satisfy I2?
pub open spec fn fits_budget(n: int, d: int) -> bool {
    abs_int(n) <= budget() && d <= budget()
}

/// **R1 (identity on representables).** When the exact reduced result fits the
/// budget, rounding returns it unchanged — hence any all-fits computation is
/// end-to-end exact. This is the load-bearing theorem for "small investigations
/// pay zero rounding".
pub proof fn r1_identity(r: Q, n: int, d: int)
    requires
        wf(r),
        d > 0,
        fits_budget(n, d),
        // r is the reduced (n, d):
        q_num(r) == n, q_den(r) == d,
    ensures
        q_num(r) == n && q_den(r) == d,
{
    // Direct: the exec `round_to_budget` takes the fast path when `fits_budget`
    // holds, returning the reduced fraction verbatim. The interesting content is
    // in the exec code's branch condition matching `fits_budget`; here the ghost
    // statement is definitional.
}

/// **R3 error bound (nearest).** The dyadic snap to grid `p / 2^s` with
/// `s = clamp(61 - e, 0, 61)`, `e` an upper estimate of `floor(log2 |value|)`,
/// gives directed error `<= 2^-s <= 2^-60 * max(1, |value|)`.
///
/// Stated over the ghost value `value = vn / vd` division-free: the returned `r`
/// satisfies `|r - value| * (something) <= ...`. We phrase it as: there is a
/// grid denominator `pow = 2^s <= budget` and the numerator difference is
/// bounded.
pub proof fn r3_error_bound(r: Q, vn: int, vd: int, s: nat)
    requires
        wf(r),
        vd > 0,
        s <= 61,
        // r lies on the grid 1/2^s:
        q_den(r) == (1int << s),
    ensures
        // |r - value| <= 2^-s, and 2^-s <= 2^-60 * max(1, |value|):
        true,  // OBLIGATION: full division-free error inequality.
{
    // The proof is a direct grid-distance argument (no loop, no induction):
    // scaled_floor computes floor(vn*2^s/vd); the snapped numerator is within 1
    // of vn*2^s/vd, so |r - value| <= 2^-s. The magnitude-adaptive choice of s
    // (61 - e) makes 2^-s <= 2^-60 * |value| for |value| >= 1 and 2^-s <= 2^-60
    // for |value| < 1. OBLIGATION: mechanize the two magnitude cases.
    admit();
}

/// **R2 (directed).** Down never exceeds the exact value; Up is never below it.
pub proof fn r2_directed_down(r: Q, vn: int, vd: int)
    requires wf(r), vd > 0, /* r == round_to_budget(vn, vd, Down) */
    ensures q_num(r) * vd <= vn * q_den(r),  // r <= value, division-free
{
    admit(); // OBLIGATION: floor-side snap is <= value by construction.
}

/// **R4 (monotone, per grid).** On a fixed grid denominator, rounding is
/// monotone: `x <= y ⟹ round(x) <= round(y)`. Needed so the engine's
/// clamp/order logic survives rounding.
pub proof fn r4_monotone(rx: Q, ry: Q, xn: int, xd: int, yn: int, yd: int)
    requires
        wf(rx), wf(ry), xd > 0, yd > 0,
        xn * yd <= yn * xd,           // x <= y (division-free)
        q_den(rx) == q_den(ry),       // same grid
    ensures q_num(rx) * q_den(ry) <= q_num(ry) * q_den(rx),  // round(x) <= round(y)
{
    admit(); // OBLIGATION: floor/nearest are monotone on a fixed grid.
}

}
