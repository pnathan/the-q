// Under development (reported non-fatal). Bézout's identity for the spec GCD —
// the foundation for Euclid's lemma and hence V1 canonical uniqueness.

use vstd::prelude::*;
use vstd::arithmetic::div_mod::lemma_fundamental_div_mod;

verus! {

pub open spec fn gcd(a: nat, b: nat) -> nat
    decreases b
{
    if b == 0 { a } else { gcd(b, (a % b) as nat) }
}

/// Bézout: there exist integer coefficients `(x, y)` with
/// `gcd(a, b) == a*x + b*y`. Proven by induction on the Euclid recursion.
pub proof fn bezout(a: nat, b: nat) -> (r: (int, int))
    ensures gcd(a, b) as int == (a as int) * r.0 + (b as int) * r.1,
    decreases b
{
    if b == 0 {
        (1int, 0int)
    } else {
        let (x1, y1) = bezout(b, (a % b) as nat);
        // gcd(a,b) == gcd(b, a%b) == b*x1 + (a%b)*y1   (definitional unfold, fuel 1)
        assert(gcd(a, b) == gcd(b, (a % b) as nat));
        // a == b*(a/b) + a%b, so a%b == a - (a/b)*b
        lemma_fundamental_div_mod(a as int, b as int);
        let quo = (a as int) / (b as int);
        let x = y1;
        let y = x1 - quo * y1;
        assert(gcd(a, b) as int == (a as int) * x + (b as int) * y) by (nonlinear_arith)
            requires
                gcd(a, b) as int == (b as int) * x1 + ((a % b) as int) * y1,
                (a as int) == (b as int) * quo + (a as int) % (b as int),
                (a % b) as int == (a as int) % (b as int),
                x == y1,
                y == x1 - quo * y1;
        (x, y)
    }
}

fn main() {}

}
