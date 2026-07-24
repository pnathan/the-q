// V5: GCD (u64 Euclid) correctness (divides both, is greatest) + termination.
//
// Standalone Verus proof file mirroring `gcd_u128`/`gcd_i64` in the shipped
// crate (src/rounding.rs, src/q.rs). It is NOT literally the shipped
// function -- it's a structurally equivalent u64 version, checked directly
// by `verus verus/gcd.rs`, kept outside the cargo package (see
// verus/smoke_test.rs for why). See TRUSTED.md for the full accounting of
// what is and isn't machine-checked.
//
// Authored and iterated on entirely via CI feedback -- no local Verus
// available (see TRUSTED.md).

use vstd::arithmetic::div_mod::lemma_fundamental_div_mod;
use vstd::prelude::*;

verus! {

/// The mathematical (ghost) GCD, defining Euclid's algorithm as a spec over
/// unbounded `nat` -- this is the "ghost model" gcd_exec is checked against.
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

/// If `d` divides `a` and `d` divides `b` (`b > 0`), `d` divides `a % b`.
/// The core fact Euclid's algorithm relies on: the common-divisor set of
/// `(a, b)` equals that of `(b, a % b)`.
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

/// `gcd_spec(a, b)` divides both `a` and `b`, for `a > 0` (the only case the
/// executable gcd below is ever called with -- `a`/`b` are magnitudes of a
/// nonzero rational's already-nonzero numerator/denominator, see
/// `rounding::round_to_budget`'s callers).
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
        // gcd_spec(a, b) == gcd_spec(b, r), which divides b and r by IH.
        // Need: it also divides a. a == b * (a / b) + r, and it divides
        // both b and r, so it divides a.
        lemma_fundamental_div_mod(a as int, b as int);
        let g = gcd_spec(b, r) as int;
        assert(a as int == b as int * (a as int / b as int) + r as int);

        // g divides b and r; expand both as explicit g-multiples so the
        // final step is pure polynomial algebra, not %/`/` reasoning
        // (mirrors the technique in lemma_divides_mod, which verified).
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

/// Any common divisor of `a` and `b` divides `gcd_spec(a, b)` -- together
/// with `lemma_gcd_divides` and positivity, this is what makes
/// `gcd_spec(a, b)` the *greatest* common divisor (any positive common
/// divisor `d` satisfies `d <= gcd_spec(a, b)` because `d` divides a
/// positive number, `lemma_divides_le` below).
proof fn lemma_gcd_greatest(a: nat, b: nat, d: int)
    requires
        a > 0,
        d > 0,
        divides(d, a as int),
        divides(d, b as int),
    ensures
        divides(d, gcd_spec(a, b) as int),
    decreases b,
{
    if b == 0 {
        assert(gcd_spec(a, b) == a);
    } else {
        let r = (a as int % b as int) as nat;
        assert(divides(d, r as int)) by {
            lemma_divides_mod(d, a as int, b as int);
        }
        lemma_gcd_greatest(b, r, d);
    }
}

proof fn lemma_divides_le(d: int, n: int)
    requires
        d > 0,
        n > 0,
        divides(d, n),
    ensures
        d <= n,
{
    lemma_fundamental_div_mod(n, d);
    assert(n == d * (n / d));
    // Proving n/d >= 1 alone doesn't close the goal -- state the actual
    // postcondition (d <= n) as the assert so its proof is in context when
    // the function returns.
    assert(d <= n) by (nonlinear_arith)
        requires
            n == d * (n / d),
            n > 0,
            d > 0,
    {}
}

/// The executable Euclidean GCD (mirrors `gcd_u128`/`gcd_i64` in the shipped
/// crate): computes `gcd_spec(a, b)` for `a > 0`, terminates (decreasing
/// `b` each iteration), and the result is a positive common divisor of `a`
/// and `b` that every other positive common divisor divides (hence is
/// greatest).
fn gcd_exec(a: u64, b: u64) -> (result: u64)
    requires
        a > 0,
    ensures
        result as nat == gcd_spec(a as nat, b as nat),
        result > 0,
        divides(result as int, a as int),
        divides(result as int, b as int),
        forall|d: int| d > 0 && divides(d, a as int) && divides(d, b as int) ==> d <= result as int,
{
    let mut x: u64 = a;
    let mut y: u64 = b;
    proof {
        lemma_gcd_divides(a as nat, b as nat);
    }
    while y != 0
        invariant
            x > 0,
            gcd_spec(x as nat, y as nat) == gcd_spec(a as nat, b as nat),
        decreases y,
    {
        let t = x % y;
        proof {
            lemma_fundamental_div_mod(x as int, y as int);
            assert(gcd_spec(x as nat, y as nat) == gcd_spec(y as nat, t as nat));
        }
        x = y;
        y = t;
    }
    proof {
        let g = gcd_spec(a as nat, b as nat) as int;
        lemma_gcd_divides(a as nat, b as nat);
        assert forall|d: int| d > 0 && divides(d, a as int) && divides(d, b as int) implies d <= x as int by {
            lemma_gcd_greatest(a as nat, b as nat, d);
            lemma_divides_le(d, g);
        }
    }
    x
}

/// V1 (canonical form): after `canonicalize` reduces `num`/`den` by
/// `g = gcd(|num|, den)`, the result `(num/g, den/g)` is coprime. This is
/// the fact that makes the shipped crate's `canonicalize_i128` (and
/// `Q::new`'s reduction) actually produce a canonical `I1` result.
proof fn lemma_reduced_is_coprime(a: nat, b: nat)
    requires
        a > 0,
    ensures
        gcd_spec(a, b) > 0,
        gcd_spec(
            (a as int / gcd_spec(a, b) as int) as nat,
            (b as int / gcd_spec(a, b) as int) as nat,
        ) == 1,
{
    lemma_gcd_divides(a, b);
    let g = gcd_spec(a, b) as int;

    // g divides a and g > 0, so a/g > 0 (a itself is > 0).
    lemma_fundamental_div_mod(a as int, g);
    assert(a as int == g * (a as int / g));
    let a2 = (a as int / g) as nat;
    let b2 = (b as int / g) as nat;
    assert(a2 > 0) by (nonlinear_arith)
        requires
            a as int == g * (a as int / g),
            a > 0,
            g > 0,
    {}

    lemma_gcd_divides(a2, b2);
    let d = gcd_spec(a2, b2) as int;
    assert(d > 0);

    // d divides a2 and b2 => g*d divides a and b (a == g*a2 == g*(d*(a2/d))).
    lemma_fundamental_div_mod(a2 as int, d);
    lemma_fundamental_div_mod(b2 as int, d);
    assert(a2 as int == d * (a2 as int / d));
    assert(b2 as int == d * (b2 as int / d));
    assert(a as int == (g * d) * (a2 as int / d)) by (nonlinear_arith)
        requires
            a as int == g * (a as int / g),
            a as int / g == a2 as int,
            a2 as int == d * (a2 as int / d),
    {}
    assert(b as int == g * b2 as int) by {
        lemma_fundamental_div_mod(b as int, g);
        assert(divides(g, b as int)) by {
            lemma_gcd_divides(a, b);
        }
        assert(b as int % g == 0);
    }
    assert(b as int == (g * d) * (b2 as int / d)) by (nonlinear_arith)
        requires
            b as int == g * b2 as int,
            b2 as int == d * (b2 as int / d),
    {}

    assert(divides(g * d, a as int)) by {
        lemma_fundamental_div_mod(a as int, g * d);
        assert(a as int == (g * d) * (a2 as int / d));
    }
    assert(divides(g * d, b as int)) by {
        lemma_fundamental_div_mod(b as int, g * d);
        assert(b as int == (g * d) * (b2 as int / d));
    }

    // g*d is a common divisor of a and b, so it divides gcd_spec(a,b) == g,
    // hence g*d <= g, hence (since g > 0) d <= 1. Combined with d > 0: d == 1.
    lemma_gcd_greatest(a, b, g * d);
    lemma_divides_le(g * d, g);
    assert(d == 1) by (nonlinear_arith)
        requires
            g * d <= g,
            g > 0,
            d > 0,
    {}
}

fn main() {}

} // verus!
