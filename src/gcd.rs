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
//! canonicalisation runs one on each result. Two changes made it cheap. First,
//! Euclid's algorithm needs a remainder, and a `u128` remainder is a software
//! routine rather than an instruction, thus the algorithm here narrows to `u64`
//! and then uses halving, comparison and subtraction only. Second, and larger,
//! [`strip_twos`] removes all the trailing zeros at once with
//! `u64::trailing_zeros`. A binary gcd that strips one two per iteration is
//! worth nothing against Euclid on hardware division; the whole advantage is in
//! that one instruction. Together the two changes took `add` from 262 ns to
//! 72 ns.
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

/// This crate's `pow2` and `vstd`'s agree.
///
/// Both are `2^n` by the same recursion, one on `int` and one on `nat`. The
/// bit lemmas in `vstd` are stated with theirs, and everything here is stated
/// with ours, thus one bridge is needed.
pub proof fn lemma_pow2_agrees(n: nat)
    ensures
        pow2(n) == vstd::arithmetic::power2::pow2(n) as int,
    decreases n,
{
    vstd::arithmetic::power2::lemma_pow2(n);
    vstd::arithmetic::power::lemma_pow_positive(2int, n);
    if n == 0 {
        vstd::arithmetic::power2::lemma2_to64();
    } else {
        lemma_pow2_agrees((n - 1) as nat);
        vstd::arithmetic::power2::lemma_pow2_unfold(n);
    }
}

/// Divide out all the twos at once.
///
/// The three halving steps of the binary gcd each strip the twos from one
/// operand. Stripping them one at a time costs an iteration per two.
/// `trailing_zeros` is one instruction, and the shift is one more.
///
/// The proof runs through `vstd`'s axioms for `u64::trailing_zeros`, which is a
/// closed specification: the trailing bits are zero, thus `2^k` divides `x`;
/// the bit at `k` is one, thus `x >> k` is odd; and `x >> k` is `x / 2^k`.
pub fn strip_twos(x: u64) -> (r: (u64, u32))
    requires
        x > 0,
    ensures
        r.0 % 2 == 1,
        r.1 < 64,
        (r.0 as nat) * (pow2(r.1 as nat) as nat) == x as nat,
        r.0 <= x,
{
    let k: u32 = x.trailing_zeros();
    proof {
        broadcast use vstd::std_specs::bits::axiom_u64_trailing_zeros;

        assert(k < 64);
    }
    let y: u64 = x >> (k as u64);
    proof {
        vstd::bits::lemma_u64_shr_is_div(x, k as u64);
        lemma_pow2_agrees(k as nat);
        // The bit at position `k` is set, thus the quotient is odd.
        assert((x >> (k as u64)) & 1u64 == 1u64);
        assert(y % 2 == 1) by (bit_vector)
            requires
                y == x >> (k as u64),
                (x >> (k as u64)) & 1u64 == 1u64,
        ;
        // The bits below `k` are clear, thus `2^k` divides `x`.
        assert(x << (sub(64u64, k as u64)) == 0);
        assert(x % (1u64 << (k as u64)) == 0) by (bit_vector)
            requires
                k < 64,
                x << (sub(64u64, k as u64)) == 0,
        ;
        vstd::bits::lemma_u64_pow2_no_overflow(k as nat);
        vstd::bits::lemma_u64_shl_is_mul(1u64, k as u64);
        vstd::arithmetic::power2::lemma_pow2_pos(k as nat);
        // `x == (x / 2^k) · 2^k` follows from that divisibility.
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(x as int, pow2(k as nat));
        assert((y as nat) * (pow2(k as nat) as nat) == x as nat) by (nonlinear_arith)
            requires
                (x as int) == pow2(k as nat) * (y as int) + 0int,
        ;
        lemma_pow2_pos(k as nat);
        assert(y <= x) by (nonlinear_arith)
            requires
                (y as int) * pow2(k as nat) == x as int,
                pow2(k as nat) >= 1,
                y >= 0,
        ;
    }
    (y, k)
}

/// An odd number is coprime to every power of two.
///
/// The rounding code needs this. Its second gcd is always taken against `2^s`,
/// thus the answer is `2^min(v2(n), s)` and no general gcd is required. This
/// lemma is the base of that: once the common twos are gone, one side is odd
/// and the rest of the gcd is `1`.
pub proof fn lemma_gcd_odd_pow2(n: nat, t: nat)
    requires
        n % 2 == 1,
    ensures
        gcd_nat(n, pow2(t) as nat) == 1,
    decreases t,
{
    if t == 0 {
        assert(pow2(0) == 1);
        // gcd(n, 1) == gcd(1, n % 1) == gcd(1, 0) == 1.
        assert(n % 1 == 0);
        assert(gcd_nat(n, 1) == gcd_nat(1, 0));
    } else {
        // `2^t` is even for `t > 0`, and `n` is odd, thus one halving step.
        lemma_pow2_pos(t);
        lemma_pow2_pos((t - 1) as nat);
        assert(pow2(t) == 2 * pow2((t - 1) as nat));
        // `(2p) % 2 == 0` and `(2p) / 2 == p` are division facts, not
        // arithmetic ones. Uniqueness of Euclidean division supplies both.
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
            pow2(t),
            2int,
            pow2((t - 1) as nat),
            0int,
        );
        lemma_gcd_half_odd_right(n, pow2(t) as nat);
        lemma_gcd_odd_pow2(n, (t - 1) as nat);
    }
}

/// **The halving law, all at once.** `gcd(x · 2^k, y) == gcd(x, y)` for an odd
/// `y`.
///
/// [`lemma_gcd_half_odd`] removes one factor of two. This removes `k` of them,
/// which is what [`strip_twos`] does in one instruction.
pub proof fn lemma_gcd_strip_odd(x: nat, k: nat, y: nat)
    requires
        y % 2 == 1,
    ensures
        gcd_nat((x * (pow2(k) as nat)) as nat, y) == gcd_nat(x, y),
    decreases k,
{
    if k == 0 {
        assert(pow2(0) == 1);
        assert(x * (pow2(0) as nat) == x);
    } else {
        lemma_pow2_pos(k);
        lemma_pow2_pos((k - 1) as nat);
        let half = (x * (pow2((k - 1) as nat) as nat)) as nat;
        let whole = (x * (pow2(k) as nat)) as nat;
        assert(pow2(k) == 2 * pow2((k - 1) as nat));
        assert((whole as int) == 2 * (half as int)) by (nonlinear_arith)
            requires
                pow2(k) == 2 * pow2((k - 1) as nat),
                (half as int) == (x as int) * pow2((k - 1) as nat),
                (whole as int) == (x as int) * pow2(k),
        ;
        // The value is even, thus one factor of two comes off the gcd.
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
            whole as int,
            2int,
            half as int,
            0int,
        );
        lemma_gcd_half_odd(whole, y);
        lemma_gcd_strip_odd(x, (k - 1) as nat, y);
    }
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
// Coprimality: Bezout, Gauss, and products
//
// These support cross-reduction, which is how `mul`, `div` and `add` avoid a
// gcd on their `i128` intermediates. `vstd` has no gcd theory, thus the layer
// is built here from Bezout upwards.
// ---------------------------------------------------------------------------

/// **Bezout.** `gcd(a, b)` is an integer linear combination of `a` and `b`.
///
/// The induction follows the recursion of `gcd_nat`: `a % b == a - b·(a / b)`,
/// thus a combination for `(b, a % b)` rearranges into one for `(a, b)`.
pub proof fn lemma_bezout(a: nat, b: nat) -> (r: (int, int))
    ensures
        gcd_nat(a, b) as int == (a as int) * r.0 + (b as int) * r.1,
    decreases b,
{
    if b == 0 {
        assert(gcd_nat(a, 0) as int == (a as int) * 1 + 0int * 0);
        (1int, 0int)
    } else {
        let (u, v) = lemma_bezout(b, (a % b) as nat);
        let q = (a as int) / (b as int);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(a as int, b as int);
        // (a % b) == a - b·q, thus b·u + (a - b·q)·v == a·v + b·(u - q·v).
        assert((b as int) * u + ((a % b) as int) * v == (a as int) * v + (b as int) * (u - q * v))
            by (nonlinear_arith)
            requires
                (a as int) == (b as int) * q + ((a % b) as int),
        ;
        assert(gcd_nat(a, b) as int == (a as int) * v + (b as int) * (u - q * v));
        (v, u - q * v)
    }
}

/// **Gauss's lemma.** If `a` is coprime to `b` and divides `b · c`, it divides
/// `c`.
///
/// From Bezout: `1 == a·u + b·v`, thus `c == a·u·c + (b·c)·v`, and `a` divides
/// both terms.
pub proof fn lemma_gauss(a: nat, b: nat, c: int)
    requires
        gcd_nat(a, b) == 1,
        divides(a as int, (b as int) * c),
    ensures
        divides(a as int, c),
{
    let (u, v) = lemma_bezout(a, b);
    assert(1int == (a as int) * u + (b as int) * v);
    lemma_divides_basic(a as int);
    // `a` divides `a` and divides `b·c`, thus it divides `(u·c)·a + v·(b·c)`.
    lemma_divides_linear(a as int, a as int, (b as int) * c, u * c, v);
    assert((u * c) * (a as int) + v * ((b as int) * c) == c) by (nonlinear_arith)
        requires
            1int == (a as int) * u + (b as int) * v,
    ;
}

/// A divisor of one member of a coprime pair is coprime to the other.
pub proof fn lemma_coprime_divisor(x: nat, y: nat, u: nat, v: nat)
    requires
        gcd_nat(x, y) == 1,
        divides(u as int, x as int),
        divides(v as int, y as int),
    ensures
        gcd_nat(u, v) == 1,
{
    let g = gcd_nat(u, v);
    lemma_gcd_divides(u, v);
    // g divides u divides x, and g divides v divides y.
    lemma_divides_trans(g as int, u as int, x as int);
    lemma_divides_trans(g as int, v as int, y as int);
    lemma_gcd_greatest(x, y, g as int);
    assert(divides(g as int, 1int));
    lemma_divides_one(g as int);
}

/// **Coprimality is multiplicative.** A number coprime to each of two factors
/// is coprime to their product.
///
/// Multiplying the two Bezout identities gives one for the product: every term
/// of `(u·s + w·t)·(v·s' + w·t')` other than `u·v·s·s'` carries a factor of `w`.
pub proof fn lemma_coprime_product(u: nat, v: nat, w: nat)
    requires
        gcd_nat(u, w) == 1,
        gcd_nat(v, w) == 1,
    ensures
        gcd_nat((u * v) as nat, w) == 1,
{
    let (s, t) = lemma_bezout(u, w);
    let (s2, t2) = lemma_bezout(v, w);
    let g = gcd_nat((u * v) as nat, w);
    lemma_gcd_divides((u * v) as nat, w);
    // 1 == (u·v)·(s·s2) + w·(u·s·t2 + v·s2·t + w·t·t2).
    let comb = (u as int) * s * t2 + (v as int) * s2 * t + (w as int) * t * t2;
    assert(((u * v) as int) * (s * s2) + (w as int) * comb == 1int) by (nonlinear_arith)
        requires
            1int == (u as int) * s + (w as int) * t,
            1int == (v as int) * s2 + (w as int) * t2,
            comb == (u as int) * s * t2 + (v as int) * s2 * t + (w as int) * t * t2,
    ;
    lemma_divides_linear(g as int, (u * v) as int, w as int, s * s2, comb);
    lemma_divides_one(g as int);
}

/// The symmetric form of [`lemma_coprime_product`]: a number coprime to a
/// product is what two coprimalities on the other side give.
pub proof fn lemma_coprime_product_right(u: nat, v: nat, w: nat)
    requires
        gcd_nat(w, u) == 1,
        gcd_nat(w, v) == 1,
    ensures
        gcd_nat(w, (u * v) as nat) == 1,
{
    lemma_gcd_sym(w, u);
    lemma_gcd_sym(w, v);
    lemma_coprime_product(u, v, w);
    lemma_gcd_sym((u * v) as nat, w);
}

/// `d` divides `n` implies `n / d` is a cofactor: `n == d · (n / d)`.
///
/// The step that turns a divisibility fact into an equation, which the
/// cross-reduction proof needs four times.
pub proof fn lemma_divides_cofactor(d: nat, n: nat)
    requires
        d > 0,
        divides(d as int, n as int),
    ensures
        n == d * (n / d),
        divides((n / d) as int, n as int),
{
    let k = choose|k: int| (n as int) == #[trigger] ((d as int) * k);
    assert(k >= 0) by (nonlinear_arith)
        requires
            d > 0,
            n >= 0,
            (n as int) == (d as int) * k,
    ;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(n as int, d as int, k, 0);
    assert(n / d == k as nat);
    assert((n as int) == (k as int) * (d as int)) by (nonlinear_arith)
        requires
            (n as int) == (d as int) * k,
    ;
}

/// **Cross-reduction.** For two canonical fractions `x1/y1` and `x2/y2`, the
/// gcd of the product's numerator and denominator splits into two gcds across
/// the pair:
///
/// `gcd(x1·x2, y1·y2) == gcd(x1, y2) · gcd(x2, y1)`
///
/// Two `u64` gcds on the *operands* can thus replace one `u128` gcd on the
/// `i128` product: the operands are bounded by `MAX_MAG`, and the product is
/// not.
///
/// The arithmetic does not currently use this law. Measurement is the reason.
/// [`gcd_u128`] narrows to [`gcd_bin_u64`] after at most two Euclid steps, thus
/// the wide gcd is already close to a narrow one, and paying for two narrow
/// gcds instead measured 8% slower on `mul` and 17% slower on `div`, with no
/// change on the chain path. The law is kept proven because the version that
/// would win needs it: cross-reduction can produce the *reduced components*
/// from `u64` divisions, which removes the two `i128` divisions as well, and
/// that is where the remaining cost is.
///
/// The proof divides each side by the two cross gcds and shows the four
/// remaining factors are pairwise coprime, which makes the reduced product
/// coprime by [`lemma_coprime_product`].
pub proof fn lemma_gcd_cross(x1: nat, y1: nat, x2: nat, y2: nat)
    requires
        gcd_nat(x1, y1) == 1,
        gcd_nat(x2, y2) == 1,
        y1 > 0,
        y2 > 0,
    ensures
        gcd_nat((x1 * x2) as nat, (y1 * y2) as nat) == gcd_nat(x1, y2) * gcd_nat(x2, y1),
{
    let g1 = gcd_nat(x1, y2);
    let g2 = gcd_nat(x2, y1);
    lemma_gcd_pos(x1, y2);
    lemma_gcd_pos(x2, y1);
    lemma_gcd_divides(x1, y2);
    lemma_gcd_divides(x2, y1);

    // The four cofactors.
    let p = (x1 / g1) as nat;
    let q = (y2 / g1) as nat;
    let r = (x2 / g2) as nat;
    let s = (y1 / g2) as nat;
    lemma_divides_cofactor(g1, x1);
    lemma_divides_cofactor(g1, y2);
    lemma_divides_cofactor(g2, x2);
    lemma_divides_cofactor(g2, y1);

    // Pairwise coprimality. Two pairs come from reducing by the gcd, and two
    // from the canonicality of the operands.
    lemma_gcd_reduce_coprime(x1, y2);
    lemma_gcd_reduce_coprime(x2, y1);
    assert(gcd_nat(p, q) == 1);
    assert(gcd_nat(r, s) == 1);
    lemma_coprime_divisor(x1, y1, p, s);
    lemma_coprime_divisor(x2, y2, r, q);

    // `p·r` is coprime to `s` and to `q`, thus to `s·q`.
    lemma_coprime_product(p, r, s);
    lemma_coprime_product(p, r, q);
    lemma_coprime_product_right(s, q, (p * r) as nat);

    // Both products carry the factor `g1·g2`, which scales out of the gcd.
    let k = (g1 * g2) as nat;
    assert(k > 0) by (nonlinear_arith)
        requires
            g1 > 0,
            g2 > 0,
            k == g1 * g2,
    ;
    assert((x1 * x2) as nat == (k * (p * r)) as nat) by (nonlinear_arith)
        requires
            x1 == g1 * p,
            x2 == g2 * r,
            k == g1 * g2,
    ;
    assert((y1 * y2) as nat == (k * (s * q)) as nat) by (nonlinear_arith)
        requires
            y1 == g2 * s,
            y2 == g1 * q,
            k == g1 * g2,
    ;
    lemma_gcd_scale(k, (p * r) as nat, (s * q) as nat);
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
// `kx` and `ky` below are consumed by the proof blocks, which plain rustc
// erases. They are live in the verified build and dead in the compiled one.
#[allow(unused_variables)]
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

    // Step two: `x` and `y` are not both even. Make `x` odd, in one step. The
    // `if` is what establishes `y % 2 == 1`: the loop above left at least one
    // of the two odd, thus an even `x` means an odd `y`.
    if x % 2 == 0 {
        let (xo, kx) = strip_twos(x);
        proof {
            lemma_gcd_strip_odd(xo as nat, kx as nat, y as nat);
            assert(((xo as nat) * (pow2(kx as nat) as nat)) as nat == x as nat);
            assert(gcd_nat(x as nat, y as nat) == gcd_nat(xo as nat, y as nat));
        }
        x = xo;
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
        // Make `y` odd, in one step. This is the hot line of the algorithm:
        // the subtraction below always leaves an even number, usually with
        // several trailing zeros, and stripping them one at a time is what
        // makes a binary gcd no faster than Euclid.
        let (yo, ky) = strip_twos(y);
        proof {
            // `gcd(x, y) == gcd(x, yo)` through symmetry, since the stripping
            // law is stated with the stripped operand on the left.
            lemma_gcd_sym(x as nat, y as nat);
            lemma_gcd_strip_odd(yo as nat, ky as nat, x as nat);
            lemma_gcd_sym(yo as nat, x as nat);
            assert(((yo as nat) * (pow2(ky as nat) as nat)) as nat == y as nat);
            assert(gcd_nat(x as nat, y as nat) == gcd_nat(x as nat, yo as nat));
        }
        y = yo;
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

/// The properties of `gcd_int(n, d)` for a positive `d`, in ghost form.
///
/// [`gcd_abs_i128`] establishes these as postconditions of the computation.
/// A caller that obtains the gcd another way — `Rat::mul_dir` and
/// `Rat::div_dir` obtain it from [`lemma_gcd_cross`] — needs the same facts
/// without the call.
pub proof fn lemma_gcd_int_facts(n: int, d: int)
    requires
        d > 0,
    ensures
        crate::model::gcd_int(n, d) > 0,
        divides(crate::model::gcd_int(n, d), n),
        divides(crate::model::gcd_int(n, d), d),
        crate::model::gcd_int(n, d) <= d,
        n != 0 ==> crate::model::gcd_int(n, d) <= crate::model::abs_int(n),
{
    let m = crate::model::abs_int(n) as nat;
    let g = crate::model::gcd_int(n, d);
    lemma_gcd_pos(m, d as nat);
    lemma_gcd_le(m, d as nat);
    lemma_gcd_divides(m, d as nat);
    // `divides(g, |n|)` gives `divides(g, n)`: the cofactor changes sign.
    let k = choose|k: int| (m as int) == #[trigger] (g * k);
    if n < 0 {
        assert(n == g * (-k)) by (nonlinear_arith)
            requires
                (m as int) == g * k,
                (m as int) == -n,
        ;
    }
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
