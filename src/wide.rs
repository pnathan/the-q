//! Verified double-word (`(hi, lo)` u128 pair) helpers: exact products and
//! shifted values beyond 128 bits, with exact comparisons. This is what lets
//! the rounding layer compare `k * ud` against `un * 2^s` exactly, with no
//! error analysis and no unverified bignum.
//!
//! Everything is phrased with `/` and `%` by `2^64`/`2^s` rather than bit
//! operations, so all proofs stay in vstd's div/mod theory.

use vstd::prelude::*;
#[allow(unused_imports)]
use vstd::arithmetic::div_mod::*;
#[allow(unused_imports)]
use vstd::arithmetic::power2::*;

verus! {

/// `2^64` as a u128.
pub const P64: u128 = 0x1_0000_0000_0000_0000;

/// Value of an `(hi, lo)` pair: `hi * 2^128 + lo`.
pub open spec fn wval(p: (u128, u128)) -> int {
    p.0 as int * 0x1_0000_0000_0000_0000_0000_0000_0000_0000 + p.1 as int
}

/// Exec power of two, equal to the spec `pow2`.
pub fn pow2_u128(e: u32) -> (r: u128)
    requires
        e <= 127,
    ensures
        r as nat == pow2(e as nat),
        r >= 1,
{
    let mut r: u128 = 1;
    let mut i: u32 = 0;
    proof {
        lemma2_to64();
    }
    while i < e
        invariant
            i <= e,
            e <= 127,
            r as nat == pow2(i as nat),
        decreases e - i,
    {
        proof {
            lemma2_to64();
            lemma2_to64_rest();
            lemma_pow2_adds(64, 63);
            assert(pow2(127) == 0x8000_0000_0000_0000_0000_0000_0000_0000);
            lemma_pow2_strictly_increases(i as nat, 127);
            lemma_pow2_unfold((i + 1) as nat);
        }
        r = r * 2;
        i = i + 1;
    }
    proof {
        lemma_pow2_pos(e as nat);
    }
    r
}

/// Exact widening product `a * b` with a small left factor (`a < 2^64`).
///
/// This is the only multiplication shape the rounding layer needs: the
/// candidate numerator `k` (63 bits) times the denominator (up to 125 bits).
pub fn wide_mul(a: u128, b: u128) -> (r: (u128, u128))
    requires
        a < P64,
    ensures
        wval(r) == a as int * b as int,
{
    let b_hi = b / P64;
    let b_lo = b % P64;
    proof {
        lemma_fundamental_div_mod(b as int, P64 as int);
        lemma_div_nonincreasing(b as int, P64 as int);
        lemma_remainder_lower(b as int, P64 as int);
        lemma_remainder_upper(b as int, P64 as int);
        // a * b_hi and a * b_lo both fit in u128.
        assert((a as int) * (b_hi as int) < 0x1_0000_0000_0000_0000_0000_0000_0000_0000)
            by (nonlinear_arith)
            requires
                a < P64,
                0 <= b_hi as int && (b_hi as int) < P64 as int;
        assert((a as int) * (b_lo as int) < 0x1_0000_0000_0000_0000_0000_0000_0000_0000)
            by (nonlinear_arith)
            requires
                a < P64,
                0 <= b_lo as int && (b_lo as int) < P64 as int;
    }
    let p1 = a * b_hi;
    let p2 = a * b_lo;
    // value = p1 * 2^64 + p2; renormalize to (hi, lo) with base-2^128 digits.
    let mid = (p1 % P64) + (p2 / P64);
    let hi = p1 / P64 + mid / P64;
    let lo = (mid % P64) * P64 + p2 % P64;
    proof {
        lemma_fundamental_div_mod(p1 as int, P64 as int);
        lemma_fundamental_div_mod(p2 as int, P64 as int);
        lemma_fundamental_div_mod(mid as int, P64 as int);
        lemma_remainder_lower(p1 as int, P64 as int);
        lemma_remainder_upper(p1 as int, P64 as int);
        lemma_remainder_lower(p2 as int, P64 as int);
        lemma_remainder_upper(p2 as int, P64 as int);
        lemma_remainder_lower(mid as int, P64 as int);
        lemma_remainder_upper(mid as int, P64 as int);
        lemma_div_nonincreasing(p1 as int, P64 as int);
        lemma_div_nonincreasing(p2 as int, P64 as int);
        lemma_div_nonincreasing(mid as int, P64 as int);
        // The (hi, lo) recombination equals p1 * 2^64 + p2.
        assert(hi as int * 0x1_0000_0000_0000_0000_0000_0000_0000_0000 + lo as int
            == p1 as int * P64 as int + p2 as int) by (nonlinear_arith)
            requires
                p1 as int == P64 as int * (p1 as int / P64 as int) + p1 as int % P64 as int,
                p2 as int == P64 as int * (p2 as int / P64 as int) + p2 as int % P64 as int,
                mid as int == P64 as int * (mid as int / P64 as int) + mid as int % P64 as int,
                mid as int == p1 as int % P64 as int + p2 as int / P64 as int,
                hi as int == p1 as int / P64 as int + mid as int / P64 as int,
                lo as int == (mid as int % P64 as int) * P64 as int + p2 as int % P64 as int,
                P64 as int * P64 as int == 0x1_0000_0000_0000_0000_0000_0000_0000_0000;
        // p1 * 2^64 + p2 == a * b.
        assert(p1 as int * P64 as int + p2 as int == a as int * b as int) by (nonlinear_arith)
            requires
                p1 as int == a as int * (b as int / P64 as int),
                p2 as int == a as int * (b as int % P64 as int),
                b as int == P64 as int * (b as int / P64 as int) + b as int % P64 as int;
    }
    (hi, lo)
}

/// Exact shifted value `a * 2^s` as an `(hi, lo)` pair, `s <= 63`.
pub fn wide_shl(a: u128, s: u32) -> (r: (u128, u128))
    requires
        s <= 63,
    ensures
        wval(r) == a as int * pow2(s as nat),
{
    let p = pow2_u128(s);
    proof {
        lemma2_to64();
        lemma2_to64_rest();
        if s < 64 {
            lemma_pow2_strictly_increases(s as nat, 64);
        }
    }
    let r = wide_mul(p, a);
    proof {
        assert(p as int * a as int == a as int * p as int) by (nonlinear_arith);
    }
    r
}

/// Exact `<=` on wide values.
pub fn wide_le(a: (u128, u128), b: (u128, u128)) -> (r: bool)
    ensures
        r == (wval(a) <= wval(b)),
{
    if a.0 < b.0 {
        true
    } else if a.0 > b.0 {
        false
    } else {
        a.1 <= b.1
    }
}

/// Exact `<` on wide values.
pub fn wide_lt(a: (u128, u128), b: (u128, u128)) -> (r: bool)
    ensures
        r == (wval(a) < wval(b)),
{
    if a.0 < b.0 {
        true
    } else if a.0 > b.0 {
        false
    } else {
        a.1 < b.1
    }
}

/// Exact `==` on wide values.
pub fn wide_eq(a: (u128, u128), b: (u128, u128)) -> (r: bool)
    ensures
        r == (wval(a) == wval(b)),
{
    a.0 == b.0 && a.1 == b.1
}

} // verus!
