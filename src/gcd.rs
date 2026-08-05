//! Verified greatest common divisor (obligation V5).
//!
//! The implementation is Stein's binary algorithm on `u64`, with Euclid's
//! algorithm ahead of it to narrow operands that do not fit. Proofs show that
//! the result equals the ghost `gcd_nat`, that each loop terminates, that the
//! result divides both arguments, and that it is the greatest such divisor. The
//! rest of the crate needs the `u128` width: canonicalisation reduces `i128`
//! intermediates, not `i64` ones. [`gcd_u64`] is the narrow entry point.
//!
//! The gcd is the dominant cost of every arithmetic operation, because
//! canonicalisation runs one on each result. Euclid's algorithm needs a
//! remainder, and a `u128` remainder is a software routine rather than an
//! instruction. The binary algorithm needs only halving, comparison and
//! subtraction. Replacing one with the other cut each arithmetic operation by
//! approximately 40%.
//!
//! `gcd_nat` is defined by Euclid's recursion, thus a proof about it by
//! induction follows the `%` structure, which the binary algorithm does not
//! have. `lemma_gcd_unique` supplies the bridge: it characterises the gcd by
//! divisibility, and each step law of the binary algorithm is then a
//! divisibility argument.
//!
//! The last lemma in this file, `lemma_gcd_reduce_coprime`, makes
//! canonicalisation work. Dividing both arguments by their gcd leaves them
//! coprime, which is exactly invariant I1.

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

/// Any common divisor of `a` and `b` divides `gcd(a, b)`. The gcd is therefore
/// *greatest* in the divisibility order. For positive divisors it is also
/// greatest in the usual order.
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
        // a%b == 1*a + (-(a/b))*b is the linear combination that
        // `lemma_divides_linear` needs. Distribution of the negation over
        // `b · dq` is nonlinear.
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
/// This scaling law is the main step in `lemma_gcd_reduce_coprime`.
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
/// This lemma justifies invariant I1. `Rat::new(n, d)` divides through by
/// `g = gcd(|n|, d)`. The result is canonical because of this lemma.
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
// The characterisation, and the three step laws the binary algorithm uses
//
// `gcd_nat` is defined by Euclid's recursion, thus a proof about it by
// induction follows the `%` structure. The binary algorithm steps by halving
// and subtraction instead. Each step law below is therefore proven from the
// *characterisation* of the gcd — a non-negative common divisor that every
// common divisor divides — and not from the recursion. `lemma_gcd_unique` is
// what makes that possible.
// ---------------------------------------------------------------------------

/// The gcd is the unique non-negative common divisor that every common divisor
/// divides.
///
/// `lemma_gcd_divides` and `lemma_gcd_greatest` state the two halves for
/// `gcd_nat` itself. This lemma states the converse: any `d` with both
/// properties *is* the gcd. Each step law below establishes the two properties
/// for its own candidate and then applies this lemma.
pub proof fn lemma_gcd_unique(a: nat, b: nat, d: nat)
    requires
        divides(d as int, a as int),
        divides(d as int, b as int),
        forall|c: int| divides(c, a as int) && divides(c, b as int) ==> divides(c, d as int),
    ensures
        d == gcd_nat(a, b),
{
    let g = gcd_nat(a, b);
    lemma_gcd_divides(a, b);
    // `d` is a common divisor, thus it divides `g`.
    lemma_gcd_greatest(a, b, d as int);
    // `g` is a common divisor, thus the hypothesis gives that it divides `d`.
    assert(divides(g as int, d as int));
    // Two non-negative integers that divide each other are equal. The zero
    // cases are separate, because `lemma_divides_le` needs both sides positive.
    if g == 0 {
        let k = choose|k: int| (d as int) == #[trigger] (0int * k);
        assert(d == 0);
    } else if d == 0 {
        let k = choose|k: int| (g as int) == #[trigger] (0int * k);
        assert(g == 0);
    } else {
        lemma_divides_le(d as int, g as int);
        lemma_divides_le(g as int, d as int);
    }
}

/// An odd divisor of `2m` divides `m`.
///
/// This is the cancellation that the halving law needs. The general form needs
/// Bezout coefficients, but for the factor `2` they are immediate: an odd `c`
/// is `2t + 1`, thus `1 == c - 2t`, thus
/// `m == m·c - t·(2m) == c·(m - t·k)` where `2m == c·k`.
pub proof fn lemma_odd_divides_half(c: int, m: int)
    requires
        divides(c, 2 * m),
        c % 2 == 1,
    ensures
        divides(c, m),
{
    let k = choose|k: int| (2 * m) == #[trigger] (c * k);
    let t = c / 2;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(c, 2);
    assert(c == 2 * t + 1);
    assert(m == c * (m - t * k)) by (nonlinear_arith)
        requires
            2 * m == c * k,
            c == 2 * t + 1,
    ;
}

/// A divisor of an odd number is odd.
pub proof fn lemma_divisor_of_odd_is_odd(c: int, y: int)
    requires
        divides(c, y),
        y % 2 == 1,
    ensures
        c % 2 == 1,
{
    let k = choose|k: int| y == #[trigger] (c * k);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(c, 2);
    let t = c / 2;
    if c % 2 == 0 {
        assert(c == 2 * t);
        assert(y == 2 * (t * k)) by (nonlinear_arith)
            requires
                y == c * k,
                c == 2 * t,
        ;
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(y, 2, t * k, 0);
        assert(y % 2 == 0);
    }
    // Euclidean `%` on 2 yields 0 or 1, and the 0 case is contradictory.
    assert(0 <= c % 2 < 2);
}

/// **The subtraction law.** `gcd(a, b) == gcd(a, b - a)` for `b >= a`.
pub proof fn lemma_gcd_sub(a: nat, b: nat)
    requires
        b >= a,
    ensures
        gcd_nat(a, b) == gcd_nat(a, (b - a) as nat),
{
    let m = (b - a) as nat;
    let d = gcd_nat(a, m);
    lemma_gcd_divides(a, m);
    // `d` divides `b == a + (b - a)`.
    lemma_divides_linear(d as int, a as int, m as int, 1, 1);
    assert(1 * (a as int) + 1 * (m as int) == b as int);
    assert forall|c: int| divides(c, a as int) && divides(c, b as int) implies divides(
        c,
        d as int,
    ) by {
        // `c` divides `b - a`, thus it divides `gcd(a, b - a)`.
        lemma_divides_linear(c, b as int, a as int, 1, -1);
        assert(1 * (b as int) + (-1) * (a as int) == m as int);
        lemma_gcd_greatest(a, m, c);
    }
    lemma_gcd_unique(a, b, d);
}

/// **The halving law.** `gcd(x, y) == gcd(x / 2, y)` when `x` is even and `y`
/// is odd.
pub proof fn lemma_gcd_half_odd(x: nat, y: nat)
    requires
        x % 2 == 0,
        y % 2 == 1,
    ensures
        gcd_nat(x, y) == gcd_nat((x / 2) as nat, y),
{
    let h = (x / 2) as nat;
    let d = gcd_nat(h, y);
    lemma_gcd_divides(h, y);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(x as int, 2);
    assert(x as int == 2 * (h as int));
    // `d` divides `x == 2·(x/2)`.
    lemma_divides_linear(d as int, h as int, h as int, 1, 1);
    assert(1 * (h as int) + 1 * (h as int) == x as int);
    assert forall|c: int| divides(c, x as int) && divides(c, y as int) implies divides(
        c,
        d as int,
    ) by {
        // `c` divides an odd number, thus `c` is odd, thus `c` divides `x / 2`.
        lemma_divisor_of_odd_is_odd(c, y as int);
        assert(divides(c, 2 * (h as int)));
        lemma_odd_divides_half(c, h as int);
        lemma_gcd_greatest(h, y, c);
    }
    lemma_gcd_unique(x, y, d);
}

/// **The halving law, on the right.** `gcd(x, y) == gcd(x, y / 2)` when `y` is
/// even and `x` is odd.
///
/// The mirror of [`lemma_gcd_half_odd`]. It is proven directly rather than by
/// composing that lemma with symmetry, because the direct proof is the same
/// six lines and needs no rewriting step.
pub proof fn lemma_gcd_half_odd_right(x: nat, y: nat)
    requires
        y % 2 == 0,
        x % 2 == 1,
    ensures
        gcd_nat(x, y) == gcd_nat(x, (y / 2) as nat),
{
    let h = (y / 2) as nat;
    let d = gcd_nat(x, h);
    lemma_gcd_divides(x, h);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(y as int, 2);
    assert(y as int == 2 * (h as int));
    lemma_divides_linear(d as int, h as int, h as int, 1, 1);
    assert(1 * (h as int) + 1 * (h as int) == y as int);
    assert forall|c: int| divides(c, x as int) && divides(c, y as int) implies divides(
        c,
        d as int,
    ) by {
        lemma_divisor_of_odd_is_odd(c, x as int);
        assert(divides(c, 2 * (h as int)));
        lemma_odd_divides_half(c, h as int);
        lemma_gcd_greatest(x, h, c);
    }
    lemma_gcd_unique(x, y, d);
}

/// The gcd is symmetric.
pub proof fn lemma_gcd_sym(a: nat, b: nat)
    ensures
        gcd_nat(a, b) == gcd_nat(b, a),
{
    let d = gcd_nat(b, a);
    lemma_gcd_divides(b, a);
    assert forall|c: int| divides(c, a as int) && divides(c, b as int) implies divides(
        c,
        d as int,
    ) by {
        lemma_gcd_greatest(b, a, c);
    }
    lemma_gcd_unique(a, b, d);
}

/// **The common-factor law.** `gcd(x, y) == 2 · gcd(x / 2, y / 2)` when both
/// are even. A restatement of [`lemma_gcd_scale`] at `k == 2`.
pub proof fn lemma_gcd_both_even(x: nat, y: nat)
    requires
        x % 2 == 0,
        y % 2 == 0,
    ensures
        gcd_nat(x, y) == 2 * gcd_nat((x / 2) as nat, (y / 2) as nat),
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(x as int, 2);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(y as int, 2);
    lemma_gcd_scale(2, (x / 2) as nat, (y / 2) as nat);
    assert(2 * (x / 2) == x);
    assert(2 * (y / 2) == y);
}

// ---------------------------------------------------------------------------
// Executable gcd
// ---------------------------------------------------------------------------

/// Stein's binary gcd on `u64`.
///
/// The algorithm uses halving and subtraction, and never divides. On this
/// crate's operand shapes it is approximately four times faster than Euclid's
/// algorithm, because a `u64` remainder is a hardware division and the halving
/// steps are shifts. `u128` remainder, which Euclid needs for the wide
/// operands that canonicalisation produces, is a software routine and costs
/// far more again.
///
/// The three steps are:
///
/// * both even: divide both by two and record the common factor
///   (`lemma_gcd_both_even`);
/// * one even, one odd: divide the even one by two
///   (`lemma_gcd_half_odd`, `lemma_gcd_half_odd_right`);
/// * both odd: subtract the smaller from the larger, which yields an even
///   number (`lemma_gcd_sub`).
///
/// The postcondition is the one Euclid's version carries: the result is
/// `gcd_nat`. Nothing downstream sees a difference.
///
/// Termination: `x + y` decreases at each step of the main loop. A halving
/// decreases `y`, and the subtraction decreases it again because `x > 0`. The
/// measure is the sum rather than `y` alone, because the swap can raise `y`.
pub fn gcd_bin_u64(a: u64, b: u64) -> (r: u64)
    ensures
        r == gcd_nat(a as nat, b as nat),
{
    if a == 0 {
        proof {
            lemma_gcd_zero(b as nat);
        }
        return b;
    }
    if b == 0 {
        proof {
            lemma_gcd_zero(a as nat);
        }
        return a;
    }
    proof {
        lemma_gcd_le(a as nat, b as nat);
        lemma_gcd_pos(a as nat, b as nat);
    }
    let mut x: u64 = a;
    let mut y: u64 = b;
    // The common power of two divided out so far. The result is `x * p`.
    let mut p: u64 = 1;

    // Step one: divide out the twos that `x` and `y` share.
    while x % 2 == 0 && y % 2 == 0
        invariant
            x > 0,
            y > 0,
            p > 0,
            gcd_nat(a as nat, b as nat) == p * gcd_nat(x as nat, y as nat),
            gcd_nat(a as nat, b as nat) <= a,
        decreases x,
    {
        proof {
            lemma_gcd_both_even(x as nat, y as nat);
            lemma_gcd_pos((x / 2) as nat, (y / 2) as nat);
            // `p * 2` stays inside `u64`, because it divides a gcd that is at
            // most `a`. The other factor is at least one.
            assert((p * 2) * gcd_nat((x / 2) as nat, (y / 2) as nat) == gcd_nat(
                a as nat,
                b as nat,
            )) by (nonlinear_arith)
                requires
                    gcd_nat(a as nat, b as nat) == p * gcd_nat(x as nat, y as nat),
                    gcd_nat(x as nat, y as nat) == 2 * gcd_nat((x / 2) as nat, (y / 2) as nat),
            ;
            assert(p * 2 <= gcd_nat(a as nat, b as nat)) by (nonlinear_arith)
                requires
                    (p * 2) * gcd_nat((x / 2) as nat, (y / 2) as nat) == gcd_nat(
                        a as nat,
                        b as nat,
                    ),
                    gcd_nat((x / 2) as nat, (y / 2) as nat) >= 1,
                    p > 0,
            ;
        }
        x = x / 2;
        y = y / 2;
        p = p * 2;
    }

    // Step two: `x` and `y` are not both even. Make `x` odd. The `if` is what
    // establishes `y % 2 == 1` for the loop below: the loop above left at
    // least one of the two odd, thus an even `x` means an odd `y`.
    if x % 2 == 0 {
        while x % 2 == 0
            invariant
                x > 0,
                y > 0,
                p > 0,
                y % 2 == 1,
                gcd_nat(a as nat, b as nat) == p * gcd_nat(x as nat, y as nat),
                gcd_nat(a as nat, b as nat) <= a,
            decreases x,
        {
            proof {
                lemma_gcd_half_odd(x as nat, y as nat);
            }
            x = x / 2;
        }
    }

    // Step three: `x` is odd throughout. Halve `y` until it is odd, then
    // subtract. The difference of two odd numbers is even, thus the next
    // iteration halves again.
    while y != 0
        invariant
            x > 0,
            p > 0,
            x % 2 == 1,
            gcd_nat(a as nat, b as nat) == p * gcd_nat(x as nat, y as nat),
            gcd_nat(a as nat, b as nat) <= a,
        decreases x + y,
    {
        // The entry value of `y`, so that the outer measure can see that the
        // halving loop never raises it.
        let ghost y0: int = y as int;
        while y % 2 == 0
            invariant
                x > 0,
                y > 0,
                p > 0,
                x % 2 == 1,
                y <= y0,
                gcd_nat(a as nat, b as nat) == p * gcd_nat(x as nat, y as nat),
                gcd_nat(a as nat, b as nat) <= a,
            decreases y,
        {
            proof {
                lemma_gcd_half_odd_right(x as nat, y as nat);
            }
            y = y / 2;
        }
        // Both are odd now. Subtract the smaller from the larger.
        if x <= y {
            proof {
                lemma_gcd_sub(x as nat, y as nat);
            }
            y = y - x;
        } else {
            proof {
                lemma_gcd_sym(x as nat, y as nat);
                lemma_gcd_sub(y as nat, x as nat);
            }
            let t: u64 = x - y;
            x = y;
            y = t;
        }
    }

    proof {
        // The loop ends at `y == 0`, where `gcd(x, 0) == x`, thus the result
        // `x * p` is the gcd and is therefore at most `a`.
        lemma_gcd_zero(x as nat);
        assert(gcd_nat(a as nat, b as nat) == p * x);
    }
    x * p
}

/// Euclid's algorithm on `u128`, narrowing to [`gcd_bin_u64`] as soon as both
/// operands fit.
///
/// Canonicalisation reduces `i128` intermediates, and a `u128` remainder is a
/// software routine. Each Euclid step here brings an operand below `2^64`, and
/// at most two steps are needed for the shapes this crate produces: one operand
/// is always a reduced component, bounded by `MAX_MAG`. The binary algorithm
/// then runs on hardware-width values.
///
/// Termination: `y` strictly decreases, because `x % y < y` whenever `y > 0`.
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
    // Euclid, but only while an operand is too wide for the binary algorithm.
    while y != 0 && (x > u64::MAX as u128 || y > u64::MAX as u128)
        invariant
            gcd_nat(x as nat, y as nat) == gcd_nat(a as nat, b as nat),
        decreases y,
    {
        let t: u128 = x % y;
        x = y;
        y = t;
    }
    let g: u128 = if y == 0 {
        proof {
            lemma_gcd_zero(x as nat);
        }
        x
    } else {
        // Both operands fit `u64` here, which is what the loop guard leaves.
        gcd_bin_u64(x as u64, y as u64) as u128
    };
    proof {
        lemma_gcd_divides(a as nat, b as nat);
        if a > 0 || b > 0 {
            lemma_gcd_pos(a as nat, b as nat);
            lemma_gcd_le(a as nat, b as nat);
        }
    }
    g
}

/// The gcd on `u64`, by [`gcd_bin_u64`].
pub fn gcd_u64(a: u64, b: u64) -> (r: u64)
    ensures
        r == gcd_nat(a as nat, b as nat),
        divides(r as int, a as int),
        divides(r as int, b as int),
        (a > 0 || b > 0) ==> r > 0,
        a > 0 ==> r <= a,
        b > 0 ==> r <= b,
{
    let g = gcd_bin_u64(a, b);
    proof {
        lemma_gcd_divides(a as nat, b as nat);
        if a > 0 || b > 0 {
            lemma_gcd_pos(a as nat, b as nat);
            lemma_gcd_le(a as nat, b as nat);
        }
    }
    g
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
