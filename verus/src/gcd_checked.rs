// Standalone, admit-free Verus proof — the CI proof target.
//
// This file is self-contained (its own crate root with `fn main`) and uses only
// canonical Verus idioms: a structurally-recursive `spec fn` with a `decreases`
// measure, and an exec loop proven to compute it via a loop invariant + its own
// `decreases`. It deliberately avoids the constructs the broader scaffold still
// owes proofs for (nonlinear bounds, bit-shifts on ghost `int`), so it is the
// one Verus artifact expected to verify green today.
//
// Run: `verus verus/src/gcd_checked.rs`

use vstd::prelude::*;

verus! {

/// Greatest common divisor (Euclid), as a total structural-recursion spec.
pub open spec fn gcd(a: nat, b: nat) -> nat
    decreases b
{
    if b == 0 { a } else { gcd(b, (a % b) as nat) }
}

/// Euclid's algorithm. Proven to compute `gcd`, and to terminate (the second
/// argument strictly decreases each iteration). This discharges obligation V5's
/// "computes the spec gcd + termination" core.
pub fn compute_gcd(a: u64, b: u64) -> (r: u64)
    ensures
        r as nat == gcd(a as nat, b as nat),
{
    let mut x: u64 = a;
    let mut y: u64 = b;
    while y != 0
        invariant
            gcd(x as nat, y as nat) == gcd(a as nat, b as nat),
        decreases y,
    {
        // One-step unfold of the spec at y != 0 (fuel 1): gcd(x,y) = gcd(y, x%y).
        assert(gcd(x as nat, y as nat) == gcd(y as nat, (x as nat % y as nat)));
        let t = x % y;
        x = y;
        y = t;
    }
    // Loop exit: y == 0, so gcd(x, 0) == x by definition.
    x
}

fn main() {}

}
