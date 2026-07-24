// GCD: Euclid on u64 (obligation V5).
//
// The exec `gcd` provably computes `spec_gcd` (loop invariant + `decreases`
// termination measure). The divisibility characterization ("divides both, is
// greatest") is developed by induction on the recursion.

use vstd::prelude::*;
use crate::model::{divides, spec_gcd};

verus! {

/// Euclid's algorithm. Terminates because the second argument strictly
/// decreases (`y` -> `x % y < y`), and computes exactly `spec_gcd`.
pub fn gcd(a: u64, b: u64) -> (r: u64)
    ensures r as nat == spec_gcd(a as nat, b as nat)
{
    let mut x: u64 = a;
    let mut y: u64 = b;
    while y != 0
        invariant spec_gcd(x as nat, y as nat) == spec_gcd(a as nat, b as nat)
        decreases y
    {
        let t = x % y;
        // Unfold one step of the spec: spec_gcd(x,y) == spec_gcd(y, x%y) for y != 0.
        assert(spec_gcd(x as nat, y as nat) == spec_gcd(y as nat, (x as nat % y as nat)));
        x = y;
        y = t;
    }
    // Loop exit: y == 0, so spec_gcd(x, 0) == x.
    x
}

/// `spec_gcd(a, b)` divides both `a` and `b`.
pub proof fn lemma_gcd_divides(a: nat, b: nat)
    ensures
        divides(spec_gcd(a, b) as int, a as int),
        divides(spec_gcd(a, b) as int, b as int),
    decreases b
{
    if b == 0 {
        // gcd(a,0) = a; a | a (k = 1) and a | 0 (k = 0).
        assert(a as int == a as int * 1int);
        assert(0int == a as int * 0int);
    } else {
        let r = (a % b) as nat;
        lemma_gcd_divides(b, r);
        // gcd(a,b) = gcd(b,r); it divides b and r, and a == (a/b)*b + r,
        // so it divides a. OBLIGATION: the "divides b ∧ divides r ⟹ divides a"
        // step via a == b*(a/b) + r (Verus `lemma_fundamental_div_mod`).
        admit();
    }
}

/// `spec_gcd(a, b)` is the *greatest* common divisor: any common divisor of `a`
/// and `b` divides it.
pub proof fn lemma_gcd_greatest(a: nat, b: nat, d: int)
    requires divides(d, a as int), divides(d, b as int),
    ensures divides(d, spec_gcd(a, b) as int),
    decreases b
{
    if b == 0 {
        // gcd = a, and d | a by hypothesis.
    } else {
        // d | b and d | a ⟹ d | (a % b); recurse on (b, a%b).
        // OBLIGATION: d | a ∧ d | b ⟹ d | a%b, then lemma_gcd_greatest(b, a%b, d).
        admit();
    }
}

}
