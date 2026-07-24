// V3: value correctness vs the ghost model -- canonicalizing `(num, den)`
// by their GCD preserves the rational VALUE (division-free
// cross-multiplication equality), for both signs of `num`. Combined with
// V1's coprimality proof (gcd.rs) this is what makes the shipped
// `canonicalize_i128` sound: same value, now in lowest terms.
//
// Standalone Verus proof file mirroring `canonicalize_i128` in
// src/rounding.rs. Checked directly via `verus verus/value_correctness.rs`;
// see verus/smoke_test.rs's header comment for why these live outside the
// cargo package. This file duplicates the small GCD divides-both lemma
// from gcd.rs (rather than a cross-file `mod`) to keep every file in
// verus/ independently self-contained, matching how CI verifies each one.
//
// Authored and iterated on entirely via CI feedback -- no local Verus
// available (see TRUSTED.md).

use vstd::arithmetic::div_mod::lemma_fundamental_div_mod;
use vstd::prelude::*;

verus! {

pub open spec fn gcd_spec(a: nat, b: nat) -> nat
    decreases b,
{
    if b == 0 {
        a
    } else {
        gcd_spec(b, (a as int % b as int) as nat)
    }
}

pub open spec fn divides(d: int, n: int) -> bool {
    n % d == 0
}

proof fn lemma_divides_mod(d: int, a: int, b: int)
    requires
        d > 0,
        b > 0,
        divides(d, a),
        divides(d, b),
    ensures
        divides(d, a % b),
{
    lemma_fundamental_div_mod(a, d);
    lemma_fundamental_div_mod(b, d);
    let pa = a / d;
    let pb = b / d;
    assert(a == d * pa);
    assert(b == d * pb);

    lemma_fundamental_div_mod(a, b);
    let q = a / b;
    let r = a % b;
    assert(a == b * q + r);

    assert(r == d * (pa - pb * q)) by (nonlinear_arith)
        requires
            a == d * pa,
            b == d * pb,
            a == b * q + r,
    {}

    lemma_fundamental_div_mod(r, d);
    assert(r == d * (r / d) + r % d);
    assert(d * (pa - pb * q) == d * (r / d) + r % d);
    assert(r % d == 0) by (nonlinear_arith)
        requires
            d * (pa - pb * q) == d * (r / d) + r % d,
    {}
}

proof fn lemma_gcd_divides(a: nat, b: nat)
    requires
        a > 0,
    ensures
        gcd_spec(a, b) > 0,
        divides(gcd_spec(a, b) as int, a as int),
        divides(gcd_spec(a, b) as int, b as int),
    decreases b,
{
    if b == 0 {
        assert(gcd_spec(a, b) == a);
    } else {
        let r = (a as int % b as int) as nat;
        lemma_gcd_divides(b, r);
        lemma_fundamental_div_mod(a as int, b as int);
        let g = gcd_spec(b, r) as int;
        assert(a as int == b as int * (a as int / b as int) + r as int);

        lemma_fundamental_div_mod(b as int, g);
        lemma_fundamental_div_mod(r as int, g);
        let pb = b as int / g;
        let pr = r as int / g;
        assert(b as int == g * pb);
        assert(r as int == g * pr);
        assert(a as int == g * (pb * (a as int / b as int) + pr)) by (nonlinear_arith)
            requires
                a as int == b as int * (a as int / b as int) + r as int,
                b as int == g * pb,
                r as int == g * pr,
        {}

        lemma_fundamental_div_mod(a as int, g);
        assert(a as int == g * (a as int / g) + a as int % g);
        assert(divides(g, a as int)) by (nonlinear_arith)
            requires
                a as int == g * (pb * (a as int / b as int) + pr),
                a as int == g * (a as int / g) + a as int % g,
        {}
    }
}

/// The key fact: `n_mag = gcd_spec(|num|, den)` divides `num` itself
/// (not just `|num|`), for either sign of `num`.
proof fn lemma_gcd_divides_signed_num(num: int, den: int)
    requires
        num != 0,
        den > 0,
    ensures
        ({
            let n_mag = if num < 0 {
                -num
            } else {
                num
            };
            let g = gcd_spec(n_mag as nat, den as nat) as int;
            g > 0 && divides(g, num)
        }),
{
    let n_mag = if num < 0 {
        -num
    } else {
        num
    };
    lemma_gcd_divides(n_mag as nat, den as nat);
    let g = gcd_spec(n_mag as nat, den as nat) as int;
    assert(divides(g, n_mag));
    lemma_fundamental_div_mod(n_mag, g);
    assert(n_mag == g * (n_mag / g));
    lemma_fundamental_div_mod(num, g);
    assert(num == g * (num / g) + num % g);
    if num < 0 {
        // num == -n_mag == -(g * (n_mag/g)) == g * (-(n_mag/g)), a
        // g-multiple; combined with the mod-range fact this forces
        // num % g == 0 (same technique as lemma_divides_mod above).
        assert(num == g * (-(n_mag / g))) by (nonlinear_arith)
            requires
                num == -n_mag,
                n_mag == g * (n_mag / g),
        {}
        assert(num % g == 0) by (nonlinear_arith)
            requires
                num == g * (-(n_mag / g)),
                num == g * (num / g) + num % g,
        {}
    } else {
        assert(num == n_mag);
        assert(num % g == 0) by (nonlinear_arith)
            requires
                num == n_mag,
                n_mag == g * (n_mag / g),
                num == g * (num / g) + num % g,
        {}
    }
}

/// V3: `canonicalize`'s reduction step preserves the rational value.
/// `(num/g, den/g)` -- the shipped `canonicalize_i128`'s result before the
/// sign-normalization step already handled separately -- represents the
/// same rational as `(num, den)`, expressed division-free via
/// cross-multiplication.
proof fn lemma_canonicalize_preserves_value(num: int, den: int)
    requires
        num != 0,
        den > 0,
    ensures
        ({
            let n_mag = if num < 0 {
                -num
            } else {
                num
            };
            let g = gcd_spec(n_mag as nat, den as nat) as int;
            (num / g) * den == num * (den / g)
        }),
{
    let n_mag = if num < 0 {
        -num
    } else {
        num
    };
    lemma_gcd_divides_signed_num(num, den);
    let g = gcd_spec(n_mag as nat, den as nat) as int;
    assert(divides(g, num));
    lemma_fundamental_div_mod(num, g);
    assert(num == g * (num / g));
    lemma_fundamental_div_mod(den, g);
    assert(den == g * (den / g));

    let num2 = num / g;
    let den2 = den / g;
    assert(num2 * den == num * den2) by (nonlinear_arith)
        requires
            num == g * num2,
            den == g * den2,
    {}
}

fn main() {}

} // verus!
