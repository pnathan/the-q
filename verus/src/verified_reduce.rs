// Under development (reported non-fatal). Batch: V5 "greatest" half (any common
// divisor divides the gcd) and V1 core (reducing by the gcd preserves value).

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

pub proof fn lemma_divides_lincomb(d: int, x: int, y: int, p: int, q: int)
    requires divides(d, x), divides(d, y),
    ensures divides(d, x * p + y * q),
{
    let kx = choose|k: int| x == #[trigger] (d * k);
    let ky = choose|k: int| y == #[trigger] (d * k);
    assert(x * p + y * q == d * (kx * p + ky * q)) by (nonlinear_arith)
        requires x == d * kx, y == d * ky;
}

/// V5 "greatest": any common divisor of `a` and `b` divides `gcd(a,b)`.
pub proof fn lemma_gcd_greatest(a: nat, b: nat, d: int)
    requires divides(d, a as int), divides(d, b as int),
    ensures divides(d, gcd(a, b) as int),
    decreases b
{
    if b == 0 {
        // gcd(a,0) == a; d | a by hypothesis.
    } else {
        lemma_fundamental_div_mod(a as int, b as int);
        // a % b == a*1 + b*(-(a/b)), so d | (a % b).
        assert((a as int) % (b as int)
            == (a as int) * 1 + (b as int) * (-((a as int) / (b as int)))) by (nonlinear_arith)
            requires a as int == (b as int) * ((a as int) / (b as int)) + (a as int) % (b as int);
        lemma_divides_lincomb(d, a as int, b as int, 1, -((a as int) / (b as int)));
        lemma_gcd_greatest(b, (a % b) as nat, d);
    }
}

/// V1 core: reducing `n/d` by a common divisor `g` preserves the value
/// (division-free: `(n/g)·d == (d/g)·n`).
pub proof fn lemma_reduce_preserves_value(n: int, d: int, g: int)
    requires g > 0, divides(g, n), divides(g, d),
    ensures (n / g) * d == (d / g) * n,
{
    let kn = choose|k: int| n == #[trigger] (g * k);
    let kd = choose|k: int| d == #[trigger] (g * k);
    // n/g == kn and d/g == kd because g divides them exactly.
    assert(n / g == kn) by (nonlinear_arith)
        requires g > 0, n == g * kn;
    assert(d / g == kd) by (nonlinear_arith)
        requires g > 0, d == g * kd;
    assert((n / g) * d == (d / g) * n) by (nonlinear_arith)
        requires n == g * kn, d == g * kd, n / g == kn, d / g == kd;
}

fn main() {}

}
