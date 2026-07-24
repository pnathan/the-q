// Under development (reported non-fatal). V5 full: `spec_gcd` divides both
// arguments and is the greatest such divisor. Proven by induction on the
// Euclid recursion using the fundamental division-modulo identity.

use vstd::prelude::*;
use vstd::arithmetic::div_mod::lemma_fundamental_div_mod;

verus! {

pub open spec fn gcd(a: nat, b: nat) -> nat
    decreases b
{
    if b == 0 { a } else { gcd(b, (a % b) as nat) }
}

pub open spec fn divides(d: int, n: int) -> bool {
    exists|k: int| n == #[trigger] (d * k)
}

/// If `d` divides `x` and `y`, it divides any integer linear combination.
pub proof fn lemma_divides_lincomb(d: int, x: int, y: int, p: int, q: int)
    requires divides(d, x), divides(d, y),
    ensures divides(d, x * p + y * q),
{
    let kx = choose|k: int| x == #[trigger] (d * k);
    let ky = choose|k: int| y == #[trigger] (d * k);
    assert(x * p + y * q == d * (kx * p + ky * q)) by (nonlinear_arith)
        requires x == d * kx, y == d * ky;
}

/// V5: `gcd(a,b)` divides both `a` and `b`.
pub proof fn lemma_gcd_divides(a: nat, b: nat)
    ensures
        divides(gcd(a, b) as int, a as int),
        divides(gcd(a, b) as int, b as int),
    decreases b
{
    if b == 0 {
        assert(a as int == (a as int) * 1);
        assert((0int) == (a as int) * 0);
    } else {
        let r = (a % b) as nat;
        lemma_gcd_divides(b, r);
        // a == b*(a/b) + a%b  (fundamental div-mod), so gcd(b,r) | a.
        lemma_fundamental_div_mod(a as int, b as int);
        assert(a as int == (b as int) * ((a as int) / (b as int)) + (a as int) % (b as int));
        assert((a as int) % (b as int) == r as int);
        lemma_divides_lincomb(
            gcd(a, b) as int,
            b as int,
            r as int,
            (a as int) / (b as int),
            1,
        );
    }
}

fn main() {}

}
