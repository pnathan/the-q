//! Verified greatest common divisor (obligation V5).
//!
//! Euclid's algorithm on `u128`, proven equal to the ghost `gcd_nat`,
//! terminating (the second argument strictly decreases), dividing both
//! arguments, and being the greatest such divisor. The `u128` width is what the
//! rest of the crate actually needs: canonicalisation reduces `i128`
//! intermediates, not `i64` ones. [`gcd_u64`] is the narrow wrapper.
//!
//! The last lemma in this file, `lemma_gcd_reduce_coprime`, is the one that
//! makes canonicalisation work at all: dividing both arguments by their gcd
//! leaves them coprime, which is exactly invariant I1.

use verus_builtin_macros::verus;

#[allow(unused_imports)]
use verus_builtin::*;
#[allow(unused_imports)]
use vstd::prelude::*;

#[allow(unused_imports)]
use crate::model::*;

verus! {

// ---------------------------------------------------------------------------
// Correctness of the ghost gcd (V5)
// ---------------------------------------------------------------------------

/// `gcd(a, b)` divides both `a` and `b`.
pub proof fn lemma_gcd_divides(a: nat, b: nat)
    ensures
        divides(gcd_nat(a, b) as int, a as int),
        divides(gcd_nat(a, b) as int, b as int),
    decreases b,
{
    if b == 0 {
        lemma_divides_basic(a as int);
    } else {
        lemma_gcd_divides(b, (a % b) as nat);
        let g = gcd_nat(b, (a % b) as nat) as int;
        assert(gcd_nat(a, b) as int == g);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(a as int, b as int);
        // a == b*(a/b) + (a%b), and g divides both b and a%b.
        lemma_divides_linear(g, b as int, (a % b) as int, (a as int) / (b as int), 1);
        assert((a as int) == (b as int) * ((a as int) / (b as int)) + (a as int) % (b as int));
        assert((a as int) % (b as int) == (a % b) as int);
    }
}

/// Any common divisor of `a` and `b` divides `gcd(a, b)` — i.e. the gcd is
/// *greatest* in the divisibility order (and hence, for positive divisors, in
/// the usual order).
pub proof fn lemma_gcd_greatest(a: nat, b: nat, c: int)
    requires
        divides(c, a as int),
        divides(c, b as int),
    ensures
        divides(c, gcd_nat(a, b) as int),
    decreases b,
{
    if b == 0 {
    } else {
        let dq = (a as int) / (b as int);
        let dr = (a as int) % (b as int);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(a as int, b as int);
        // a%b == 1*a + (-(a/b))*b — the linear combination `lemma_divides_linear`
        // needs. Distributing the negation over `b · dq` is nonlinear.
        assert(dr == 1 * (a as int) + (-dq) * (b as int)) by (nonlinear_arith)
            requires
                (a as int) == (b as int) * dq + dr,
        ;
        lemma_divides_linear(c, a as int, b as int, 1, -dq);
        assert((a as int) % (b as int) == (a % b) as int);
        lemma_gcd_greatest(b, (a % b) as nat, c);
    }
}

/// The gcd is positive unless both arguments are zero.
pub proof fn lemma_gcd_pos(a: nat, b: nat)
    requires
        a > 0 || b > 0,
    ensures
        gcd_nat(a, b) > 0,
    decreases b,
{
    if b == 0 {
    } else {
        if (a % b) > 0 {
            lemma_gcd_pos(b, (a % b) as nat);
        } else {
            lemma_gcd_pos(b, (a % b) as nat);
        }
    }
}

/// `gcd(a, b) <= a` when `a > 0`, and `<= b` when `b > 0`.
pub proof fn lemma_gcd_le(a: nat, b: nat)
    requires
        a > 0 || b > 0,
    ensures
        a > 0 ==> gcd_nat(a, b) <= a,
        b > 0 ==> gcd_nat(a, b) <= b,
{
    lemma_gcd_pos(a, b);
    lemma_gcd_divides(a, b);
    if a > 0 {
        lemma_divides_le(gcd_nat(a, b) as int, a as int);
    }
    if b > 0 {
        lemma_divides_le(gcd_nat(a, b) as int, b as int);
    }
}

/// `gcd(a, 0) == a` and `gcd(a, a) == a`.
pub proof fn lemma_gcd_zero(a: nat)
    ensures
        gcd_nat(a, 0) == a,
        gcd_nat(0, a) == a,
{
    if a == 0 {
    } else {
        assert(gcd_nat(0, a) == gcd_nat(a, (0nat % a) as nat));
        assert(0nat % a == 0nat);
    }
}

/// `gcd(k·a, k·b) == k · gcd(a, b)` for `k > 0`.
///
/// The workhorse behind `lemma_gcd_reduce_coprime`.
pub proof fn lemma_gcd_scale(k: nat, a: nat, b: nat)
    requires
        k > 0,
    ensures
        gcd_nat((k * a) as nat, (k * b) as nat) == (k * gcd_nat(a, b)) as nat,
    decreases b,
{
    if b == 0 {
        assert(k * b == 0);
        lemma_gcd_zero((k * a) as nat);
    } else {
        // (k*a) % (k*b) == k * (a % b), by uniqueness of Euclidean division.
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(a as int, b as int);
        let q = (a as int) / (b as int);
        let r = (a as int) % (b as int);
        assert(0 <= r < b as int);
        assert((k * a) as int == (k * b) as int * q + (k as int) * r) by (nonlinear_arith)
            requires
                (a as int) == (b as int) * q + r,
        ;
        assert(0 <= (k as int) * r < (k * b) as int) by (nonlinear_arith)
            requires
                k > 0,
                0 <= r < b as int,
        ;
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
            (k * a) as int,
            (k * b) as int,
            q,
            (k as int) * r,
        );
        assert((k * a) as nat % (k * b) as nat == (k * (a % b)) as nat);
        lemma_gcd_scale(k, b, (a % b) as nat);
    }
}

/// Dividing both arguments by their gcd leaves them coprime.
///
/// This is invariant I1's justification: `Rat::new(n, d)` divides through by
/// `g = gcd(|n|, d)` and the result is canonical precisely because of this.
pub proof fn lemma_gcd_reduce_coprime(a: nat, b: nat)
    requires
        a > 0 || b > 0,
    ensures
        gcd_nat((a / gcd_nat(a, b)) as nat, (b / gcd_nat(a, b)) as nat) == 1,
{
    let g = gcd_nat(a, b);
    lemma_gcd_pos(a, b);
    lemma_gcd_divides(a, b);
    // g divides a and b, so a == g * (a/g) and b == g * (b/g).
    let ka = choose|k: int| a as int == #[trigger] ((g as int) * k);
    let kb = choose|k: int| b as int == #[trigger] ((g as int) * k);
    assert(ka >= 0 && kb >= 0) by (nonlinear_arith)
        requires
            g > 0,
            a >= 0,
            b >= 0,
            a as int == (g as int) * ka,
            b as int == (g as int) * kb,
    ;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(a as int, g as int, ka, 0);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(b as int, g as int, kb, 0);
    assert(a / g == ka as nat);
    assert(b / g == kb as nat);
    lemma_gcd_scale(g, ka as nat, kb as nat);
    // gcd(g·ka, g·kb) == g · gcd(ka, kb), and the left side is gcd(a,b) == g.
    // Naming the cofactor keeps the cancellation a plain `g·q == g·1`.
    let q = gcd_nat(ka as nat, kb as nat);
    assert(g * ka == a && g * kb == b) by (nonlinear_arith)
        requires
            a as int == (g as int) * ka,
            b as int == (g as int) * kb,
            ka >= 0,
            kb >= 0,
    ;
    assert(g * q == g * 1);
    assert(q == 1) by (nonlinear_arith)
        requires
            g > 0,
            g * q == g * 1,
    ;
}

// ---------------------------------------------------------------------------
// Executable gcd
// ---------------------------------------------------------------------------

/// Euclid's algorithm on `u128`.
///
/// Termination: `y` strictly decreases (`x % y < y` whenever `y > 0`), which is
/// the `decreases` measure on the loop. No arithmetic here can overflow — `%`
/// only ever shrinks its operands.
pub fn gcd_u128(a: u128, b: u128) -> (r: u128)
    ensures
        r == gcd_nat(a as nat, b as nat),
        divides(r as int, a as int),
        divides(r as int, b as int),
        (a > 0 || b > 0) ==> r > 0,
        a > 0 ==> r <= a,
        b > 0 ==> r <= b,
{
    let mut x: u128 = a;
    let mut y: u128 = b;
    while y != 0
        invariant
            gcd_nat(x as nat, y as nat) == gcd_nat(a as nat, b as nat),
        decreases y,
    {
        let t: u128 = x % y;
        x = y;
        y = t;
    }
    proof {
        lemma_gcd_zero(x as nat);
        lemma_gcd_divides(a as nat, b as nat);
        if a > 0 || b > 0 {
            lemma_gcd_pos(a as nat, b as nat);
            lemma_gcd_le(a as nat, b as nat);
        }
    }
    x
}

/// Euclid's algorithm on `u64`; a thin wrapper over [`gcd_u128`].
pub fn gcd_u64(a: u64, b: u64) -> (r: u64)
    ensures
        r == gcd_nat(a as nat, b as nat),
        divides(r as int, a as int),
        divides(r as int, b as int),
        (a > 0 || b > 0) ==> r > 0,
        a > 0 ==> r <= a,
        b > 0 ==> r <= b,
{
    let g = gcd_u128(a as u128, b as u128);
    proof {
        if a > 0 {
            lemma_gcd_le(a as nat, b as nat);
        } else if b > 0 {
            lemma_gcd_le(a as nat, b as nat);
        } else {
            lemma_gcd_zero(0nat);
        }
    }
    g as u64
}

/// `gcd(|n|, d)` for a signed numerator and a positive denominator, the exact
/// shape canonicalisation needs.
pub fn gcd_abs_i128(n: i128, d: i128) -> (r: i128)
    requires
        d > 0,
        -0x4000_0000_0000_0000_0000_0000_0000_0000i128 < n,
    ensures
        r > 0,
        r == crate::model::gcd_int(n as int, d as int),
        divides(r as int, n as int),
        divides(r as int, d as int),
        r <= d,
        n != 0 ==> r <= crate::model::abs_int(n as int),
{
    let m: u128 = if n < 0 {
        (0 - n) as u128
    } else {
        n as u128
    };
    let g = gcd_u128(m, d as u128);
    proof {
        lemma_gcd_pos(m as nat, d as nat);
        lemma_gcd_le(m as nat, d as nat);
        lemma_gcd_divides(m as nat, d as nat);
        // divides(g, |n|) implies divides(g, n).
        let k = choose|k: int| (m as int) == #[trigger] ((g as int) * k);
        if n < 0 {
            assert((n as int) == (g as int) * (-k)) by (nonlinear_arith)
                requires
                    (m as int) == (g as int) * k,
                    (m as int) == -(n as int),
            ;
        }
    }
    g as i128
}

} // verus!
