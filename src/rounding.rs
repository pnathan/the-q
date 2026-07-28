//! Canonicalization and the directed-rounding contract (spec §3, obligation V4).
//!
//! Every public arithmetic op funnels its exact `i128` numerator/denominator
//! through [`from_exact_i128`]: if the gcd-reduced exact result already fits
//! the `I2` budget it is returned unchanged (**R1**, identity on
//! representables -- any computation whose exact values all fit the budget
//! is therefore end-to-end exact, with zero rounding). Otherwise
//! [`round_to_budget`] snaps it to the nearest (or directed) dyadic fraction
//! `k / 2^s` with `s` chosen so `k` and `2^s` both fit `I2`.
//!
//! ## The rounding algorithm (dyadic snap)
//!
//! Let `m = bitlen(|num|)`, `l = bitlen(den)` for the coprime, sign-normalized
//! exact pair. `m - l` approximates `log2(|value|)`. We choose the shift
//! `s = clamp(61 - (m - l), 0, 61)` so the scaled magnitude `|value| * 2^s`
//! lands near `2^61` -- one bit of headroom below the `I2` ceiling of
//! `2^62 - 1`, so a rounding carry never itself overflows the budget.
//!
//! The scaled magnitude is computed by **binary long division**
//! (`q0 = |num| / den`, then `s` more bits by repeatedly doubling the
//! remainder), never by shifting `|num|` directly -- `|num|` can already be
//! up to ~2^125 bits wide (see the overflow table in the spec / crate
//! README), and `|num| << 61` would overflow `i128` long before the
//! division ever runs. The remainder is always `< den`, so each doubling
//! step is bounded by `2 * den`, which is safe in `u128` for any `den` that
//! itself fits `i128`.
//!
//! `R3` (error `<= 2^-60 * max(1, |exact|)`) follows from `s >= 60` whenever
//! the value's magnitude is `<= 1`; for larger magnitudes the same *relative*
//! bound holds because `s` shrinks exactly as fast as the magnitude grows
//! (`m - l` term). `R4` (monotone) holds because floor/ceil/round-half-away-
//! from-zero of `value * 2^s` are each monotone in `value` for fixed `s`, and
//! `s` itself is a monotone (non-increasing) function of `value`'s magnitude
//! -- verified empirically in `tests/property.rs`, not yet machine-checked.
//!
//! ## Magnitude ceiling (a spec clarification, not in the original text)
//!
//! `I2` bounds `|num| <= 2^62 - 1` directly, not just precision: a rational
//! value's magnitude is a lower bound on `|num|` for *any* valid
//! denominator (`|num| = |value| * den >= |value|`). So if the exact
//! mathematical result of an op has magnitude `> 2^62 - 1`, no canonical `Q`
//! -- rounded or not -- can represent it, even approximately within `R3`
//! (the error bound is relative to a magnitude the result itself could never
//! reach). The spec's own sizing analysis (§4.4) notes this never happens in
//! the consuming engine (opinion values stay in `[0, 1]`), so this is a
//! theoretical edge only. This implementation **saturates** to
//! `±(2^62 - 1)/1` in that case rather than panicking, documented here and
//! covered by `tests/adversarial.rs`. `Down`/`Up` directedness cannot be
//! honored past the ceiling (there is no representable value on the correct
//! side); `Nearest` saturation is the honest closest answer.

use crate::q::Q;
use vstd::prelude::*;

/// `2^62 - 1`, the `I2` bound on both `|num|` and `den`.
pub const MAX_MAGNITUDE: i64 = (1i64 << 62) - 1;
const MAX_MAGNITUDE_U128: u128 = MAX_MAGNITUDE as u128;

/// Directed rounding mode. `Down`/`Up` bracket the exact value (`R2`);
/// `Nearest` is what all plain arithmetic ops use.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Dir {
    Down,
    Up,
    Nearest,
}

verus! {

// vstd's proof fns (like this one) only exist as compiled items when
// verus_keep_ghost is set (i.e. when the real `verus` tool is doing the
// compiling, as in CI's `verus` job) -- under plain `cargo build`/`test`,
// the whole crate compiles without that cfg, so this import (and every
// `proof { ... }` block that calls it, all erased the same way under plain
// rustc) must be gated identically or `cargo build` fails to resolve it.
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::div_mod::lemma_fundamental_div_mod;

// Trusted bridge to std (spec_ext / TRUSTED.md-tracked axiom, not a Verus
// proof obligation): vstd doesn't model `i128::unsigned_abs` out of the
// box. Its behavior (`|x|` as a `u128`) is exactly what the name says and
// is trivially checked by tests/property.rs's I2-invariant checks on
// every op that calls it, so trusting the standard library's own
// documented behavior here is the same kind of bridge `to_f64` already is
// (see TRUSTED.md).
pub assume_specification[i128::unsigned_abs](x: i128) -> (result: u128)
    ensures
        result == if x < 0 {
            (-x) as u128
        } else {
            x as u128
        },
;

// V5 (GCD correctness + termination) and the V1/V3 support lemmas below
// are proved directly against the shipped `gcd_u128`/`canonicalize_i128`
// -- not a standalone mirror (contrast `verus/gcd.rs`, `verus/
// value_correctness.rs`, which prove the same facts about transcriptions
// because this inline wiring wasn't believed achievable when they were
// written; see TRUSTED.md for the full history).

/// The mathematical (ghost) GCD: Euclid's algorithm as a spec over
/// unbounded `nat`, the "ghost model" `gcd_u128` is checked against.
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

pub open spec fn iabs(x: int) -> int {
    if x < 0 {
        -x
    } else {
        x
    }
}

/// If `d` divides `a` and `d` divides `b` (`b > 0`), `d` divides `a % b`.
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

/// `gcd_spec(a, b)` divides both `a` and `b`, for `a > 0`.
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

/// Any common divisor of `a` and `b` divides `gcd_spec(a, b)`.
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
    assert(d <= n) by (nonlinear_arith)
        requires
            n == d * (n / d),
            n > 0,
            d > 0,
    {}
}

/// V5 (GCD correctness + termination): `result` is `gcd_spec(a, b)` --
/// positive, divides both `a` and `b`, and every other positive common
/// divisor divides it (hence it's the greatest).
fn gcd_u128(mut a: u128, mut b: u128) -> (result: u128)
    requires
        a > 0,
    ensures
        result as nat == gcd_spec(a as nat, b as nat),
        result > 0,
        divides(result as int, a as int),
        divides(result as int, b as int),
        forall|d: int|
            d > 0 && divides(d, a as int) && divides(d, b as int) ==> d <= result as int,
{
    let ghost a0 = a as nat;
    let ghost b0 = b as nat;
    proof {
        lemma_gcd_divides(a0, b0);
    }
    while b != 0
        invariant
            a > 0,
            gcd_spec(a as nat, b as nat) == gcd_spec(a0, b0),
        decreases b,
    {
        let t = a % b;
        proof {
            lemma_fundamental_div_mod(a as int, b as int);
            assert(gcd_spec(a as nat, b as nat) == gcd_spec(b as nat, t as nat));
        }
        a = b;
        b = t;
    }
    proof {
        let g = gcd_spec(a0, b0) as int;
        lemma_gcd_divides(a0, b0);
        assert forall|d: int| d > 0 && divides(d, a0 as int) && divides(d, b0 as int) implies d
            <= a as int by {
            lemma_gcd_greatest(a0, b0, d);
            lemma_divides_le(d, g);
        }
    }
    a
}

/// V1: `gcd_spec(a, b)` divides `a`, so dividing both by it yields a
/// coprime pair -- the fact that makes `canonicalize_i128`'s reduction
/// step actually produce `I1`-canonical output.
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

    lemma_fundamental_div_mod(a as int, g);
    assert(a as int == g * (a as int / g));
    assert(a as int / g > 0) by (nonlinear_arith)
        requires
            a as int == g * (a as int / g),
            a > 0,
            g > 0,
    {}
    let a2 = (a as int / g) as nat;
    let b2 = (b as int / g) as nat;
    assert(a2 > 0);

    lemma_gcd_divides(a2, b2);
    let d = gcd_spec(a2, b2) as int;
    assert(d > 0);

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
    assert(divides(g, b as int)) by {
        lemma_gcd_divides(a, b);
    }
    lemma_fundamental_div_mod(b as int, g);
    assert(b as int == g * (b as int / g) + b as int % g);
    assert(b as int == g * b2 as int) by (nonlinear_arith)
        requires
            b as int == g * (b as int / g) + b as int % g,
            b as int % g == 0,
            b as int / g == b2 as int,
    {}
    assert(b as int == (g * d) * (b2 as int / d)) by (nonlinear_arith)
        requires
            b as int == g * b2 as int,
            b2 as int == d * (b2 as int / d),
    {}

    lemma_fundamental_div_mod(a as int, g * d);
    assert(a as int == (g * d) * (a as int / (g * d)) + a as int % (g * d));
    assert(divides(g * d, a as int)) by (nonlinear_arith)
        requires
            a as int == (g * d) * (a2 as int / d),
            a as int == (g * d) * (a as int / (g * d)) + a as int % (g * d),
    {}
    lemma_fundamental_div_mod(b as int, g * d);
    assert(b as int == (g * d) * (b as int / (g * d)) + b as int % (g * d));
    assert(divides(g * d, b as int)) by (nonlinear_arith)
        requires
            b as int == (g * d) * (b2 as int / d),
            b as int == (g * d) * (b as int / (g * d)) + b as int % (g * d),
    {}

    lemma_gcd_greatest(a, b, g * d);
    lemma_divides_le(g * d, g);
    assert(d == 1) by (nonlinear_arith)
        requires
            g * d <= g,
            g > 0,
            d > 0,
    {}
}

/// V3: canonicalizing `(num, den)` by their GCD preserves the rational
/// value (division-free cross-multiplication).
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
    lemma_gcd_divides(n_mag as nat, den as nat);
    let g = gcd_spec(n_mag as nat, den as nat) as int;

    lemma_fundamental_div_mod(n_mag, g);
    assert(n_mag == g * (n_mag / g));
    lemma_fundamental_div_mod(num, g);
    assert(num == g * (num / g) + num % g);
    if num < 0 {
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

/// Sign-normalize (`den > 0`) and GCD-reduce an exact `num/den` pair.
/// Requires `den != 0`; `num != i128::MIN` and `den != i128::MIN` are the
/// honest preconditions negation needs (never violated by any real
/// caller: every intermediate this function is actually called with is
/// bounded by ~2^125, per `ops.rs`'s overflow table, far short of
/// `i128::MIN`'s `2^127` magnitude). `0` always canonicalizes to `(0, 1)`.
///
/// V1 + V3: the result is `I1`-canonical (`den > 0`, coprime, and
/// `num == 0 ==> den == 1`) and represents the same rational value as the
/// input, stated division-free via cross-multiplication.
fn canonicalize_i128(num: i128, den: i128) -> (result: (i128, i128))
    requires
        den != 0,
        num != i128::MIN,
        den != i128::MIN,
    ensures
        result.1 > 0,
        result.0 == 0 ==> result.1 == 1,
        result.0 as int * den as int == num as int * result.1 as int,
        result.0 != 0 ==> gcd_spec(iabs(result.0 as int) as nat, result.1 as nat) == 1,
{
    let (n2, d2) = if den < 0 { (-num, -den) } else { (num, den) };
    assert(d2 > 0);
    assert(n2 as int * den as int == num as int * d2 as int) by (nonlinear_arith)
        requires
            (den < 0 && n2 == -num && d2 == -den) || (den >= 0 && n2 == num && d2 == den),
    {}
    if n2 == 0 {
        // n2 is a plain negation/copy of num (never a product), so this
        // is direct sign reasoning, not a factoring argument -- avoid
        // routing it through the cross-multiplication equation above.
        // (The two arms erase to identical exec-mode no-ops -- both
        // asserts are proof-only -- which is why clippy sees them as
        // `if_same_then_else`; the ghost-mode content genuinely differs.)
        #[allow(clippy::if_same_then_else)]
        if den < 0 {
            assert(n2 == -num);
        } else {
            assert(n2 == num);
        }
        assert(num == 0);
        assert(0int * den as int == num as int * 1int);
        (0, 1)
    } else {
        proof {
            lemma_canonicalize_preserves_value(n2 as int, d2 as int);
            lemma_reduced_is_coprime(iabs(n2 as int) as nat, d2 as nat);
        }
        let n2_mag = n2.unsigned_abs();
        let g_mag = gcd_u128(n2_mag, d2 as u128);
        proof {
            // g_mag divides n2_mag (n2_mag > 0, since n2 != 0 here), so
            // g_mag <= n2_mag <= i128::MAX as u128 (n2 != i128::MIN is a
            // precondition) -- the u128 -> i128 cast below can't overflow.
            lemma_divides_le(g_mag as int, n2_mag as int);
        }
        let g = g_mag as i128;
        proof {
            // d2/g > 0: g divides d2 (gcd_u128's ensures on its `b`
            // argument), and d2 = g*(d2/g) with both d2, g > 0.
            lemma_fundamental_div_mod(d2 as int, g as int);
            assert(d2 as int == g as int * (d2 as int / g as int));
            assert(d2 as int / g as int > 0) by (nonlinear_arith)
                requires
                    d2 as int == g as int * (d2 as int / g as int),
                    d2 > 0,
                    g > 0,
            {}
            // n2/g != 0: same reasoning via n2_mag = g*(n2_mag/g) > 0.
            lemma_fundamental_div_mod(n2_mag as int, g as int);
            assert(n2_mag as int == g as int * (n2_mag as int / g as int));
            assert(n2_mag as int / g as int > 0) by (nonlinear_arith)
                requires
                    n2_mag as int == g as int * (n2_mag as int / g as int),
                    n2_mag > 0,
                    g > 0,
            {}

            // n2 == g * (n2/g) exactly: g divides n2_mag, and g divides n2
            // itself regardless of sign (same sign-case technique as
            // lemma_canonicalize_preserves_value, reproduced concretely
            // here rather than relying on substituting into that lemma's
            // abstracted conclusion).
            lemma_fundamental_div_mod(n2 as int, g as int);
            assert(n2 as int == g as int * (n2 as int / g as int) + n2 as int % g as int);
            if n2 < 0 {
                assert(n2 as int == g as int * (-(n2_mag as int / g as int))) by (nonlinear_arith)
                    requires
                        n2 as int == -(n2_mag as int),
                        n2_mag as int == g as int * (n2_mag as int / g as int),
                {}
                assert(n2 as int % g as int == 0) by (nonlinear_arith)
                    requires
                        n2 as int == g as int * (-(n2_mag as int / g as int)),
                        n2 as int == g as int * (n2 as int / g as int) + n2 as int % g as int,
                {}
            } else {
                assert(n2 as int % g as int == 0) by (nonlinear_arith)
                    requires
                        n2 as int == n2_mag as int,
                        n2_mag as int == g as int * (n2_mag as int / g as int),
                        n2 as int == g as int * (n2 as int / g as int) + n2 as int % g as int,
                {}
            }
            assert(n2 as int == g as int * (n2 as int / g as int));
        }
        // Computed via the *unsigned* magnitude quotient with sign applied
        // explicitly, rather than `n2 / g` (signed i128 division) directly:
        // Verus's built-in bridge from exec `/` to ghost `int` division
        // isn't automatic for negative-numerator signed division the way
        // it is for the (always-nonnegative here) unsigned case, so this
        // sidesteps that gap entirely rather than fighting it. `n2 / g`
        // and this expression compute the identical value regardless
        // (division is exact -- proven above -- so truncating and
        // Euclidean division coincide), so this is still what
        // `canonicalize_i128` actually ships.
        //
        // The whole cross-multiplication goal is proven here, *before*
        // out0/out1 are let-bound below, in terms of n2_over_g/d2/g
        // directly (including one bare, non-nonlinear_arith assert
        // spelling out the exact conditional expression out0 will be
        // defined as). Proving a fact about an already-let-bound alias
        // and then returning that alias in a sibling `if` arm does not
        // reliably connect back to the caller's postcondition in this
        // Verus version -- proving it in terms of the pre-let expressions
        // first, then aliasing via a trivial `let` right before the
        // return, does. (Verified empirically against a series of
        // minimized reproductions; not something to unlearn without
        // re-testing against a newer Verus release.)
        let n2_over_g = n2_mag / g_mag;
        proof {
            assert(n2_over_g as int == n2_mag as int / g_mag as int);
            assert(n2_mag as int == g as int * (n2_over_g as int)) by (nonlinear_arith)
                requires
                    n2_mag as int == g as int * (n2_mag as int / g as int),
                    n2_over_g as int == n2_mag as int / g_mag as int,
                    g as int == g_mag as int,
            {}
            assert(d2 as int / g as int == d2 as int / g as int);
            assert(n2 as int == g as int * (if n2 < 0 {
                -(n2_over_g as int)
            } else {
                n2_over_g as int
            })) by (nonlinear_arith)
                requires
                    n2_mag as int == g as int * (n2_over_g as int),
                    n2 as int == n2_mag as int || n2 as int == -(n2_mag as int),
                    (n2 < 0) == (n2 as int == -(n2_mag as int)),
            {}
            // n2 == g*out0, d2 == g*(d2/g), and n2*den == num*d2
            // (established before the branch) combine via
            // g*(out0*den) == g*(num*(d2/g)), then cancel g (g > 0).
            assert(g as int * ((if n2 < 0 {
                -(n2_over_g as int)
            } else {
                n2_over_g as int
            }) * den as int) == g as int * (num as int * (d2 as int / g as int))) by (
            nonlinear_arith)
                requires
                    n2 as int == g as int * (if n2 < 0 {
                        -(n2_over_g as int)
                    } else {
                        n2_over_g as int
                    }),
                    d2 as int == g as int * (d2 as int / g as int),
                    n2 as int * den as int == num as int * d2 as int,
            {}
            assert((if n2 < 0 {
                -(n2_over_g as int)
            } else {
                n2_over_g as int
            }) * den as int == num as int * (d2 as int / g as int)) by (nonlinear_arith)
                requires
                    g as int * ((if n2 < 0 {
                        -(n2_over_g as int)
                    } else {
                        n2_over_g as int
                    }) * den as int) == g as int * (num as int * (d2 as int / g as int)),
                    g > 0,
            {}
        }
        // out1 first (no case split needed), then out0 via an if/else
        // *expression* whose arms are each fully i128-typed (sidesteps an
        // E0308 caused by nesting an if/else under `as int`). Each arm
        // restates its exact value's contribution to the goal via a bare
        // assert immediately before the tail expression, and after out0 is
        // bound the goal is restated once more in terms of out0/out1
        // directly -- empirically, the postcondition checker doesn't
        // reliably connect facts proven about a tail expression's arms back
        // through the enclosing tuple literal `(out0, out1)` without this
        // final explicit restatement immediately before the return.
        let out1: i128 = d2 / g;
        assert(out1 as int == d2 as int / g as int);
        let out0: i128 = if n2 < 0 {
            assert((-(n2_over_g as i128)) as int * den as int == num as int * out1 as int);
            -(n2_over_g as i128)
        } else {
            assert((n2_over_g as i128) as int * den as int == num as int * out1 as int);
            n2_over_g as i128
        };
        assert(out0 as int * den as int == num as int * out1 as int);
        (out0, out1)
    }
}

} // verus!

fn fits_budget(num: i128, den: i128) -> bool {
    num.unsigned_abs() <= MAX_MAGNITUDE_U128 && (den as u128) <= MAX_MAGNITUDE_U128
}

fn bitlen_u128(x: u128) -> u32 {
    u128::BITS - x.leading_zeros()
}

/// Round a coprime, sign-normalized, out-of-budget `num/den` (`den > 0`) to
/// the nearest (or directed) representable `Q`, per `R1`-`R4` and the
/// magnitude-ceiling clarification above.
fn round_to_budget(num: i128, den: i128, dir: Dir) -> Q {
    debug_assert!(den > 0);
    debug_assert!(num != 0, "round_to_budget: 0 is always in-budget");
    debug_assert!(
        !fits_budget(num, den),
        "round_to_budget called on an in-budget value"
    );

    let sign_negative = num < 0;
    let n_mag = num.unsigned_abs();
    let d_mag = den as u128;

    let m = bitlen_u128(n_mag) as i64;
    let l = bitlen_u128(d_mag) as i64;
    // Target: scaled magnitude ~ 2^61 (one bit of headroom under the 2^62-1
    // ceiling to absorb a rounding-up carry).
    let s = (61 - (m - l)).clamp(0, 61) as u32;

    let mut q_mag = n_mag / d_mag;
    let mut r = n_mag % d_mag;
    for _ in 0..s {
        r *= 2;
        if r >= d_mag {
            r -= d_mag;
            q_mag = q_mag * 2 + 1;
        } else {
            q_mag *= 2;
        }
    }
    let exact = r == 0;

    // Direction is expressed on the *value*, not the magnitude: for a
    // negative value, "round down" (toward -inf) means rounding the
    // magnitude *up*.
    let round_down_mag = match dir {
        Dir::Nearest => false, // handled separately below
        Dir::Down => !sign_negative,
        Dir::Up => sign_negative,
    };

    let k_mag: u128 = if exact {
        q_mag
    } else if matches!(dir, Dir::Nearest) {
        // Round half away from zero (in magnitude terms).
        if 2 * r >= d_mag {
            q_mag + 1
        } else {
            q_mag
        }
    } else if round_down_mag {
        q_mag
    } else {
        q_mag + 1
    };

    let (mut k_mag, mut s) = (k_mag, s);
    if k_mag == 0 {
        return Q::zero();
    }
    if k_mag > MAX_MAGNITUDE_U128 {
        // Magnitude ceiling (see module docs): no representable Q, at any
        // shift, can hold a value this large. Only reachable at s == 0 --
        // s > 0 implies q_mag was already <= 2^61-ish by construction, so a
        // rounding-up carry keeps it within the 2^62-1 ceiling. Saturate.
        k_mag = MAX_MAGNITUDE_U128;
        s = 0;
    } else {
        // Reduce k_mag / 2^s by common power-of-two factors.
        let tz = k_mag.trailing_zeros().min(s);
        k_mag >>= tz;
        s -= tz;
    }

    let num_out = if sign_negative {
        -(k_mag as i128)
    } else {
        k_mag as i128
    };
    let den_out = 1i128 << s;
    debug_assert!(fits_budget(num_out, den_out));

    Q::from_canonical_i128(num_out, den_out)
}

/// Canonicalize an exact `num/den` pair and round it into budget if needed.
/// This is the single funnel every arithmetic op uses.
pub(crate) fn from_exact_i128(num: i128, den: i128, dir: Dir) -> Q {
    let (num, den) = canonicalize_i128(num, den);
    if fits_budget(num, den) {
        Q::from_canonical_i128(num, den)
    } else {
        round_to_budget(num, den, dir)
    }
}
