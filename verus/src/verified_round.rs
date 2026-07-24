// Under development (reported non-fatal). V4 rounding contract at the grid
// level: floor/ceil snapping of a value n/d onto the dyadic grid 1/2^s.
//
//   R2 (directed): floor-snap <= value <= ceil-snap.
//   R3 (grid error, division-free): 0 <= n·2^s − q·d < d, i.e. the snap is
//       within one grid step 1/2^s of the exact value.
//   R1 (identity): a value already on the grid snaps to itself exactly.
//
// Proven on ghost `int` (unbounded — the exec `round_to_budget` uses bitwise
// long division to compute the same q without overflow); all facts are stated
// division-free via the fundamental division-modulo identity.

use vstd::prelude::*;
use vstd::arithmetic::div_mod::{lemma_fundamental_div_mod, lemma_div_multiples_vanish};

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

/// **R2 (Down) + R3 (grid error)** for the floor-snap `q = ⌊n·2^s / d⌋`:
///   `q·d ≤ n·2^s < q·d + d`
/// i.e. `q/2^s ≤ n/d` (floor is below the value) and the gap is `< 1/2^s`.
pub proof fn snap_floor_bounds(n: int, d: int, s: nat)
    requires d >= 1,
    ensures
        ((n * (pow2(s) as int)) / d) * d <= n * (pow2(s) as int),
        n * (pow2(s) as int) < ((n * (pow2(s) as int)) / d) * d + d,
{
    pow2_pos(s);
    let p = pow2(s) as int;
    lemma_fundamental_div_mod(n * p, d);
    let q = (n * p) / d;
    let r = (n * p) % d;
    // lemma gives: n*p == d*q + r  and  0 <= r < d
    assert(q * d <= n * p) by (nonlinear_arith) requires n * p == d * q + r, 0 <= r;
    assert(n * p < q * d + d) by (nonlinear_arith) requires n * p == d * q + r, r < d;
}

/// **R2 (Up)** for the ceil-snap `qc = q + [r>0]`: `n·2^s ≤ qc·d` and the gap
/// `qc·d − n·2^s ≤ d`. Together with `snap_floor_bounds`, brackets the value:
/// floor-snap ≤ value ≤ ceil-snap.
pub proof fn snap_ceil_bounds(n: int, d: int, s: nat)
    requires d >= 1,
    ensures ({
        let p = pow2(s) as int;
        let q = (n * p) / d;
        let r = (n * p) % d;
        let qc = if r > 0 { q + 1 } else { q };
        &&& n * p <= qc * d
        &&& qc * d <= n * p + d
    }),
{
    pow2_pos(s);
    let p = pow2(s) as int;
    lemma_fundamental_div_mod(n * p, d);
    let q = (n * p) / d;
    let r = (n * p) % d;
    let qc = if r > 0 { q + 1 } else { q };
    assert(n * p <= qc * d) by (nonlinear_arith)
        requires n * p == d * q + r, 0 <= r < d, qc == if r > 0 { q + 1 } else { q };
    assert(qc * d <= n * p + d) by (nonlinear_arith)
        requires n * p == d * q + r, 0 <= r < d, qc == if r > 0 { q + 1 } else { q };
}

/// **R1 (identity on representables)**: if the value `n/d` already lies on the
/// grid (`n·2^s == p0·d`), the floor-snap returns exactly `p0`.
pub proof fn snap_floor_exact(n: int, d: int, s: nat, p0: int)
    requires d >= 1, n * (pow2(s) as int) == p0 * d,
    ensures (n * (pow2(s) as int)) / d == p0,
{
    pow2_pos(s);
    lemma_div_multiples_vanish(p0, d);   // (p0*d)/d == p0
    assert((n * (pow2(s) as int)) / d == (p0 * d) / d);
}

fn main() {}

}
