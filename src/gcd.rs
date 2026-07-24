//! Verified GCD: spec-level lemma suite (divisibility, Bézout,
//! canonicalization) and the executable Euclid loop (obligation V5).

use vstd::prelude::*;
#[allow(unused_imports)]
use vstd::arithmetic::div_mod::*;

#[allow(unused_imports)]
use crate::specs::*;

verus! {

// ---------------------------------------------------------------------------
// Divisibility helpers
// ---------------------------------------------------------------------------

/// Exact division: if `d | n` and `d > 0` then `n == d * (n / d)`.
pub proof fn lemma_div_exact(d: nat, n: nat)
    requires
        divides(d, n),
        d > 0,
    ensures
        n == d * (n / d),
{
    let k = choose|k: nat| n == #[trigger] (d * k);
    lemma_div_multiples_vanish(k as int, d as int);
    assert(n as int / d as int == k as int);
}

/// A divisor of a positive number is no larger than it.
pub proof fn lemma_divides_le(d: nat, n: nat)
    requires
        divides(d, n),
        n > 0,
    ensures
        0 < d <= n,
{
    let k = choose|k: nat| n == #[trigger] (d * k);
    assert(0 < d <= n) by (nonlinear_arith)
        requires n == d * k, n > 0;
}

// ---------------------------------------------------------------------------
// GCD basics
// ---------------------------------------------------------------------------

/// The gcd divides both of its arguments.
pub proof fn lemma_gcd_divides(a: nat, b: nat)
    ensures
        divides(gcd(a, b), a),
        divides(gcd(a, b), b),
    decreases b,
{
    if b == 0 {
        assert(a == a * 1);
        assert(0nat == a * 0);
    } else {
        lemma_gcd_divides(b, a % b);
        let g = gcd(b, a % b);
        let k1 = choose|k: nat| b == #[trigger] (g * k);
        let k2 = choose|k: nat| (a % b) == #[trigger] (g * k);
        lemma_fundamental_div_mod(a as int, b as int);
        let q = a as int / b as int;
        lemma_div_pos_is_pos(a as int, b as int);
        assert(a as int == g as int * (q * k1 as int + k2 as int)) by (nonlinear_arith)
            requires
                a as int == q * b as int + (a % b) as int,
                b == g * k1,
                (a % b) as nat == g * k2;
        let ka = (q * k1 as int + k2 as int) as nat;
        assert(a == gcd(a, b) * ka);
    }
}

/// The gcd of a pair with a positive member is positive.
pub proof fn lemma_gcd_pos(a: nat, b: nat)
    requires
        a > 0 || b > 0,
    ensures
        gcd(a, b) > 0,
    decreases b,
{
    if b == 0 {
    } else {
        lemma_gcd_pos(b, a % b);
    }
}

/// Bézout coefficients, constructively: `a * x + b * y == gcd(a, b)`.
pub proof fn lemma_bezout(a: nat, b: nat) -> (r: (int, int))
    ensures
        a as int * r.0 + b as int * r.1 == gcd(a, b) as int,
    decreases b,
{
    if b == 0 {
        assert(a as int * 1 + b as int * 0 == a as int) by (nonlinear_arith);
        (1int, 0int)
    } else {
        let (x, y) = lemma_bezout(b, a % b);
        lemma_fundamental_div_mod(a as int, b as int);
        let q = a as int / b as int;
        assert(a as int * y + b as int * (x - q * y) == gcd(b, a % b) as int) by (nonlinear_arith)
            requires
                b as int * x + (a % b) as int * y == gcd(b, a % b) as int,
                (a % b) as int == a as int - q * b as int;
        (y, x - q * y)
    }
}

/// Any common divisor divides the gcd (the "greatest" in gcd, strong form).
pub proof fn lemma_common_divisor_divides_gcd(d: nat, a: nat, b: nat)
    requires
        divides(d, a),
        divides(d, b),
    ensures
        divides(d, gcd(a, b)),
{
    let ka = choose|k: nat| a == #[trigger] (d * k);
    let kb = choose|k: nat| b == #[trigger] (d * k);
    if d == 0 {
        assert(a == 0) by (nonlinear_arith) requires a == 0 * ka;
        assert(b == 0) by (nonlinear_arith) requires b == 0 * kb;
        assert(gcd(0, 0) == 0);
        assert(0nat == 0 * 0);
    } else {
        let (x, y) = lemma_bezout(a, b);
        let m = ka as int * x + kb as int * y;
        assert(gcd(a, b) as int == d as int * m) by (nonlinear_arith)
            requires
                m == ka as int * x + kb as int * y,
                a == d * ka,
                b == d * kb,
                a as int * x + b as int * y == gcd(a, b) as int;
        assert(m >= 0) by (nonlinear_arith)
            requires d as int * m == gcd(a, b) as int, d > 0, gcd(a, b) as int >= 0;
        assert(gcd(a, b) == d * (m as nat));
    }
}

/// gcd is symmetric.
pub proof fn lemma_gcd_symm(a: nat, b: nat)
    ensures
        gcd(a, b) == gcd(b, a),
{
    lemma_gcd_divides(a, b);
    lemma_gcd_divides(b, a);
    lemma_common_divisor_divides_gcd(gcd(a, b), b, a);
    lemma_common_divisor_divides_gcd(gcd(b, a), a, b);
    if gcd(a, b) == 0 {
        let k = choose|k: nat| gcd(b, a) == #[trigger] (gcd(a, b) * k);
        assert(gcd(b, a) == 0) by (nonlinear_arith) requires gcd(b, a) == 0 * k;
    } else if gcd(b, a) == 0 {
        let k = choose|k: nat| gcd(a, b) == #[trigger] (gcd(b, a) * k);
        assert(gcd(a, b) == 0) by (nonlinear_arith) requires gcd(a, b) == 0 * k;
    } else {
        lemma_divides_le(gcd(a, b), gcd(b, a));
        lemma_divides_le(gcd(b, a), gcd(a, b));
    }
}

/// Canonicalization: dividing out the gcd leaves a coprime pair.
pub proof fn lemma_gcd_div_gcd_is_one(a: nat, b: nat)
    requires
        gcd(a, b) > 0,
    ensures
        gcd(a / gcd(a, b), b / gcd(a, b)) == 1,
{
    let g = gcd(a, b);
    lemma_gcd_divides(a, b);
    lemma_div_exact(g, a);
    lemma_div_exact(g, b);
    let a1 = a / g;
    let b1 = b / g;
    let h = gcd(a1, b1);
    // h > 0: a and b are not both zero (else g would be 0).
    if a == 0 && b == 0 {
        assert(gcd(0, 0) == 0);
        assert(false);
    }
    if a > 0 {
        assert(a1 > 0) by (nonlinear_arith) requires a == g * a1, a > 0;
    } else {
        assert(b1 > 0) by (nonlinear_arith) requires b == g * b1, b > 0;
    }
    lemma_gcd_pos(a1, b1);
    // g * h divides both a and b.
    lemma_gcd_divides(a1, b1);
    let ka = choose|k: nat| a1 == #[trigger] (h * k);
    let kb = choose|k: nat| b1 == #[trigger] (h * k);
    assert(a == (g * h) * ka) by (nonlinear_arith) requires a == g * a1, a1 == h * ka;
    assert(b == (g * h) * kb) by (nonlinear_arith) requires b == g * b1, b1 == h * kb;
    assert(divides(g * h, a));
    assert(divides(g * h, b));
    lemma_common_divisor_divides_gcd(g * h, a, b);
    lemma_divides_le(g * h, g);
    assert(h == 1) by (nonlinear_arith) requires g * h <= g, g > 0, h >= 1;
}

/// Euclid's lemma (Gauss form): if `gcd(n, d1) == 1` and `n * d2 == m * d1`,
/// then `d1 | d2`.
pub proof fn lemma_coprime_divides(n: nat, d1: nat, d2: nat, m: nat)
    requires
        gcd(n, d1) == 1,
        n * d2 == m * d1,
    ensures
        divides(d1, d2),
{
    if d1 == 0 {
        // gcd(n, 0) == n == 1, so d2 == m * 0 == 0; 0 | 0.
        assert(gcd(n, 0nat) == n);
        assert(d2 == m * 0) by (nonlinear_arith) requires n * d2 == m * 0, n == 1;
        assert(0nat == 0 * 0);
    } else {
        let (x, y) = lemma_bezout(n, d1);
        // d2 == d2 * (n x + d1 y) == x (n d2) + d1 y d2 == x (m d1) + d1 y d2
        //    == d1 (x m + y d2)
        let k = x * m as int + y * d2 as int;
        assert(d2 as int == d1 as int * k) by (nonlinear_arith)
            requires
                k == x * m as int + y * d2 as int,
                n as int * x + d1 as int * y == 1,
                n as int * d2 as int == m as int * d1 as int;
        assert(k >= 0) by (nonlinear_arith)
            requires d1 as int * k == d2 as int, d1 > 0, d2 as int >= 0;
        assert(d2 == d1 * (k as nat));
    }
}

/// `gcd(a, 1) == 1`.
pub proof fn lemma_gcd_x_one(a: nat)
    ensures
        gcd(a, 1) == 1,
{
    assert(a % 1 == 0);
    assert(gcd(a, 1) == gcd(1, 0));
}

// ---------------------------------------------------------------------------
// Executable GCD (V5)
// ---------------------------------------------------------------------------

/// Euclid's algorithm on u128, proven to compute the spec `gcd`.
pub fn gcd_u128(a: u128, b: u128) -> (g: u128)
    ensures
        g as nat == gcd(a as nat, b as nat),
{
    let mut x = a;
    let mut y = b;
    while y != 0
        invariant
            gcd(x as nat, y as nat) == gcd(a as nat, b as nat),
        decreases y,
    {
        let r = x % y;
        proof {
            assert(gcd(x as nat, y as nat) == gcd(y as nat, (x as nat) % (y as nat)));
        }
        x = y;
        y = r;
    }
    x
}

} // verus!
