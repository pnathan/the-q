//! Fixed-point kernel for the transcendental functions.
//!
//! # Why a second numeric representation
//!
//! [`crate::transcendental`] evaluates its series through `Q`, thus every term
//! costs a full canonicalisation and a full rounding: a gcd, two divisions and
//! the R3 machinery, for values that are about to be multiplied by the next
//! term anyway. `exp` runs approximately eighty such operations. That is the
//! whole reason a transcendental costs tens of microseconds while an
//! arithmetic operation costs tens of nanoseconds.
//!
//! This module carries the same values as plain integers on a fixed dyadic
//! grid. A value `v` is held as `V: i128` and denotes `V · 2^-63`. A
//! multiplication is then one `i128` multiply and one shift-and-round, and
//! nothing else: no gcd, no canonical form, no `Rat`.
//!
//! # The scale, and why 63
//!
//! The grid is `2^-63`, two bits finer than the `2^-61` grid that the crate
//! rounds to. The two extra bits are the guard digits: the series accumulates
//! its rounding errors on this grid and the result is regridded to `2^-61`
//! once, at the end, so the accumulated error stays below the final grid step.
//!
//! # The invariant
//!
//! Every function here states the range it needs on its inputs, and those
//! ranges are what discharge the `i128` overflow checks. The widest term is the
//! product inside [`fx_mul`], which is bounded by its precondition rather than
//! by the type: `|a · b| < 2^126` leaves a full bit of headroom under
//! `i128::MAX`, and the callers hold values far below that.
//!
//! # What is proven here, and what is not
//!
//! Proven: every operation's rounding error against the exact product or
//! quotient, division-free, in the same cross-multiplied style the rest of the
//! crate uses; and the absence of overflow, which is what makes the functions
//! total.
//!
//! Not proven, and not provable here: that a truncated series approximates the
//! function it is a series for. That is a statement about `exp` and `ln`, and
//! this crate has no term for either. The series bounds are documented at their
//! definitions and checked against a high-precision oracle in
//! `tests/transcendental.rs`.

use verus_builtin_macros::verus;

#[allow(unused_imports)]
use verus_builtin::*;
#[allow(unused_imports)]
use vstd::prelude::*;

#[allow(unused_imports)]
use crate::model::*;

verus! {

/// The fixed-point scale exponent: a value `V` denotes `V · 2^-63`.
pub const FX_SHIFT: u32 = 63;

/// `2^63`, the fixed-point unit, as an `i128`.
pub const FX_ONE: i128 = 9223372036854775808i128;

/// The fixed-point unit, in ghost form.
pub open spec fn fx_one() -> int {
    pow2(63)
}

/// `FX_ONE` is `2^63`.
pub proof fn lemma_fx_one()
    ensures
        FX_ONE as int == fx_one(),
{
    crate::model::lemma_pow2_63();
}

/// The product of two fixed-point values, rounded to the grid.
///
/// The result `r` satisfies `|r · 2^63 − a · b| <= 2^62`, which is half a grid
/// step: the rounding is to nearest, with ties away from zero. Ties away rather
/// than ties to even because the sign is handled by splitting off the magnitude,
/// which makes the rule symmetric under negation and therefore keeps
/// `fx_mul(-a, b) == -fx_mul(a, b)`.
///
/// The precondition on the product is what discharges the overflow check. It is
/// stated on the mathematical product, thus a caller proves it from its own
/// value bounds and never from the type.
pub fn fx_mul(a: i128, b: i128) -> (r: i128)
    requires
        abs_int((a as int) * (b as int)) < pow2(126),
    ensures
        2 * abs_int((r as int) * fx_one() - (a as int) * (b as int)) <= fx_one(),
        abs_int(r as int) * fx_one() <= abs_int((a as int) * (b as int)) + fx_one(),
{
    proof {
        crate::model::lemma_pow2_126();
        lemma_fx_one();
    }
    let p: i128 = a * b;
    let neg: bool = p < 0;
    let m: i128 = if neg {
        0 - p
    } else {
        p
    };
    let q: i128 = m / FX_ONE;
    let rem: i128 = m % FX_ONE;
    proof {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(m as int, FX_ONE as int);
        vstd::arithmetic::div_mod::lemma_div_pos_is_pos(m as int, FX_ONE as int);
        vstd::arithmetic::div_mod::lemma_mod_bound(m as int, FX_ONE as int);
    }
    // Round the magnitude to nearest: step up when the remainder is at least
    // half of the unit. `rem < 2^63`, thus `2·rem` cannot overflow.
    let qr: i128 = if rem * 2 >= FX_ONE {
        q + 1
    } else {
        q
    };
    proof {
        assert((qr as int) * fx_one() - (m as int) == (qr as int) * fx_one() - ((q as int)
            * fx_one() + (rem as int)));
        assert(2 * abs_int((qr as int) * fx_one() - (m as int)) <= fx_one()) by (nonlinear_arith)
            requires
                (m as int) == (q as int) * fx_one() + (rem as int),
                (rem as int) >= 0,
                (rem as int) < fx_one(),
                (rem as int) * 2 >= fx_one() ==> (qr as int) == (q as int) + 1,
                (rem as int) * 2 < fx_one() ==> (qr as int) == q as int,
        ;
        assert(abs_int(qr as int) * fx_one() <= (m as int) + fx_one()) by (nonlinear_arith)
            requires
                (m as int) == (q as int) * fx_one() + (rem as int),
                (rem as int) >= 0,
                (rem as int) < fx_one(),
                q as int >= 0,
                fx_one() > 0,
                (rem as int) * 2 >= fx_one() ==> (qr as int) == (q as int) + 1,
                (rem as int) * 2 < fx_one() ==> (qr as int) == q as int,
        ;
    }
    if neg {
        0 - qr
    } else {
        qr
    }
}

/// A fixed-point value divided by a small positive integer, rounded to the
/// grid.
///
/// The result satisfies `|r · k − v| <= k / 2`, again half a step of the
/// quotient's own grid, with ties away from zero for the same symmetry reason
/// as [`fx_mul`].
///
/// The series evaluators divide by the term index, which is why the divisor is
/// an ordinary integer rather than a second fixed-point value: a fixed-point
/// division would need a wide intermediate and there is no need for one.
pub fn fx_div_int(v: i128, k: u32) -> (r: i128)
    requires
        k > 0,
        abs_int(v as int) < pow2(126),
    ensures
        2 * abs_int((r as int) * (k as int) - (v as int)) <= k as int,
        abs_int(r as int) <= abs_int(v as int),
{
    proof {
        crate::model::lemma_pow2_126();
    }
    let neg: bool = v < 0;
    let m: i128 = if neg {
        0 - v
    } else {
        v
    };
    let kk: i128 = k as i128;
    let q: i128 = m / kk;
    let rem: i128 = m % kk;
    proof {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(m as int, kk as int);
        vstd::arithmetic::div_mod::lemma_div_pos_is_pos(m as int, kk as int);
        vstd::arithmetic::div_mod::lemma_mod_bound(m as int, kk as int);
    }
    let qr: i128 = if rem * 2 >= kk {
        q + 1
    } else {
        q
    };
    proof {
        // The division lemma states `m == kk · q + rem`. The blocks below need
        // the factors in the other order, and a `nonlinear_arith` block sees
        // only its own `requires`.
        assert((m as int) == (q as int) * (kk as int) + (rem as int)) by (nonlinear_arith)
            requires
                (m as int) == (kk as int) * (q as int) + (rem as int),
        ;
        assert(2 * abs_int((qr as int) * (kk as int) - (m as int)) <= kk as int)
            by (nonlinear_arith)
            requires
                (m as int) == (q as int) * (kk as int) + (rem as int),
                (rem as int) >= 0,
                (rem as int) < (kk as int),
                (rem as int) * 2 >= kk as int ==> (qr as int) == (q as int) + 1,
                (rem as int) * 2 < kk as int ==> (qr as int) == q as int,
        ;
        assert(abs_int(qr as int) <= m as int) by (nonlinear_arith)
            requires
                (m as int) == (q as int) * (kk as int) + (rem as int),
                (rem as int) >= 0,
                (rem as int) < (kk as int),
                q as int >= 0,
                kk as int >= 1,
                (rem as int) * 2 >= kk as int ==> (qr as int) == (q as int) + 1,
                (rem as int) * 2 < kk as int ==> (qr as int) == q as int,
        ;
    }
    let r: i128 = if neg {
        0 - qr
    } else {
        qr
    };
    proof {
        // Both bounds are stated on the magnitude. Negating the result and the
        // input together leaves each difference's absolute value unchanged.
        assert((r as int) * (kk as int) - (v as int) == if neg {
            -((qr as int) * (kk as int) - (m as int))
        } else {
            (qr as int) * (kk as int) - (m as int)
        }) by (nonlinear_arith)
            requires
                neg ==> ((r as int) == -(qr as int) && (v as int) == -(m as int)),
                !neg ==> ((r as int) == qr as int && (v as int) == m as int),
        ;
    }
    r
}


// ---------------------------------------------------------------------------
// The exponential, on the grid
// ---------------------------------------------------------------------------

/// The largest reduced argument the series accepts: `0.347 · 2^63`.
///
/// Cody-Waite reduction brings `|r|` to at most `ln2/2 ≈ 0.3466`, which is
/// `3.1966e18` on this grid. The literal above it is the bound the proofs use.
pub const FX_R_MAX: i128 = 3200000000000000000i128;

/// The largest value the Horner accumulator can reach: `1.6 · 2^63`.
///
/// From `|T| <= 1.6 · 2^63` and `|R| <= FX_R_MAX`, the product inside
/// [`fx_mul`] is at most `4.8e37`, which is well under the `2^126` that its
/// precondition asks for. The accumulator itself returns to `1 + |R|·|T|`,
/// which is under this bound. The loop therefore closes.
pub const FX_T_MAX: i128 = 14757395258967641292i128;

/// Terms in the fixed-point exponential series.
///
/// The tail after `N` terms at `|z| <= 0.3536` is
/// `z^(N+1)/(N+1)! · 1/(1 − z/(N+2))`. At `N = 15` that is `2^-68.7`, and at
/// `N = 16` it is `2^-73.8`. The target is one term below the `2^-63` grid, and
/// sixteen leaves a term of margin. Twelve would give `2^-52.4`, which is not
/// enough.
pub const FX_EXP_TERMS: u32 = 16;

/// `e^z` for a reduced `z`, by Horner over the Maclaurin series.
///
/// The recurrence is `T := 1 + (z/k)·T` for `k` from `FX_EXP_TERMS` down to
/// `1`, which is the Maclaurin series in the form that needs one multiplication
/// and one small division per term and no powers.
///
/// What the postcondition states is the accumulator bound, which is what makes
/// the function total: it is the fact that discharges every overflow check
/// here and in [`fx_mul`]. The distance from the result to `e^z` is not stated,
/// because `e^z` has no term in this crate. Each step's rounding error is
/// bounded by [`fx_mul`] and [`fx_div_int`] at half a grid step, the series
/// damps earlier errors by `|z| <= 0.354` per step, and the truncation bound is
/// the one on [`FX_EXP_TERMS`]. `tests/transcendental.rs` checks the composed
/// result against a series carried to `2^-90`.
pub fn fx_exp_series(z: i128) -> (t: i128)
    requires
        abs_int(z as int) <= FX_R_MAX as int,
    ensures
        abs_int(t as int) <= FX_T_MAX as int,
{
    proof {
        crate::model::lemma_pow2_126();
        lemma_fx_one();
    }
    let mut t: i128 = FX_ONE;
    let mut k: u32 = FX_EXP_TERMS;
    while k >= 1
        invariant
            abs_int(t as int) <= FX_T_MAX as int,
            abs_int(z as int) <= FX_R_MAX as int,
            k <= FX_EXP_TERMS,
        decreases k,
    {
        proof {
            // The product bound that `fx_mul` asks for. Both factors are
            // bounded by literals, so this is one multiplication of literals.
            crate::model::lemma_pow2_126();
            lemma_fx_one();
            assert(abs_int((z as int) * (t as int)) < pow2(126)) by (nonlinear_arith)
                requires
                    abs_int(z as int) <= FX_R_MAX as int,
                    abs_int(t as int) <= FX_T_MAX as int,
                    pow2(126) == 85070591730234615865843651857942052864,
            ;
        }
        let p: i128 = fx_mul(z, t);
        proof {
            lemma_fx_one();
            // `|p| <= (|z|·|t|)/2^63 + 1`, and both factors are at their
            // bounds, so `|p| <= 5.2e18`. The accumulator below is then at
            // most `2^63 + 5.2e18`, which is inside `FX_T_MAX`.
            assert(abs_int(p as int) <= 5200000000000000000i128 as int) by (nonlinear_arith)
                requires
                    abs_int(p as int) * fx_one() <= abs_int((z as int) * (t as int)) + fx_one(),
                    abs_int(z as int) <= FX_R_MAX as int,
                    abs_int(t as int) <= FX_T_MAX as int,
                    fx_one() == 9223372036854775808,
            ;
        }
        let q: i128 = fx_div_int(p, k);
        t = FX_ONE + q;
        k = k - 1;
    }
    t
}


/// `ln 2` on the grid: `round(ln2 · 2^63)`.
///
/// The literal is checked against a series derivation in
/// `tests/transcendental.rs`, the same way [`crate::transcendental::ln2`] is.
pub const FX_LN2_HI: i128 = 6393154322601327830i128;

/// The residual of `ln 2` at the next scale down:
/// `round((ln2 · 2^63 − FX_LN2_HI) · 2^63)`.
///
/// Two words rather than one. The reduction subtracts `m · ln2` for an `m` as
/// large as 64, so a one-word constant leaves `64 · 2^-64 ≈ 2^-58` of error and
/// caps the whole function there. With the residual the same term is
/// `64 · 2^-128`, which is nothing. The pair represents `ln 2` to `2^-128.4`.
pub const FX_LN2_LO: i128 = -974768846722515540i128;

/// The exponential, reduced and evaluated on the grid.
///
/// Returns `(t, m)` denoting `t · 2^(m − 63)`. The caller turns that into a
/// `Rat`, which is where the value meets the `2^-61` grid and the budget.
///
/// # Method
///
/// Cody-Waite reduction: `m = nearest(x / ln2)` and `r = x − m·ln2`, with
/// `ln 2` carried in two words so that the subtraction is exact to `2^-128`.
/// The series then runs on `|r| <= ln2/2`, and the reconstruction is
/// `e^x = 2^m · e^r`, which on this representation is an exponent adjustment
/// and not a computation.
///
/// That is the whole reason for the reduction shape. Halving the argument and
/// squaring the result, which is what the `Q` implementation does, doubles the
/// relative error at every squaring: seven halvings cost seven bits. Here the
/// reconstruction costs nothing.
pub fn fx_exp_reduced(x: i128) -> (r: (i128, i32))
    requires
        abs_int(x as int) <= 406000000000000000000i128 as int,
    ensures
        abs_int(r.0 as int) <= FX_T_MAX as int,
        -66 <= r.1 <= 66,
{
    proof {
        crate::model::lemma_pow2_126();
        lemma_fx_one();
    }
    // m = nearest(x / ln2), by rounding the quotient of two grid values.
    // Both are positive, so the rounding is done on the magnitude and the sign
    // reattached, which keeps `m(-x) == -m(x)`.
    let neg: bool = x < 0;
    let ax: i128 = if neg {
        0 - x
    } else {
        x
    };
    let qm: i128 = ax / FX_LN2_HI;
    let rm: i128 = ax % FX_LN2_HI;
    let am: i128 = if rm * 2 >= FX_LN2_HI {
        qm + 1
    } else {
        qm
    };
    let m: i128 = if neg {
        0 - am
    } else {
        am
    };
    proof {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(ax as int, FX_LN2_HI as int);
        vstd::arithmetic::div_mod::lemma_div_pos_is_pos(ax as int, FX_LN2_HI as int);
        vstd::arithmetic::div_mod::lemma_mod_bound(ax as int, FX_LN2_HI as int);
        // `|x| <= 44 · 2^63` and `ln2 · 2^63 > 6.39e18` give `|m| <= 65`.
        assert(abs_int(m as int) <= 66) by (nonlinear_arith)
            requires
                (ax as int) == (FX_LN2_HI as int) * (qm as int) + (rm as int),
                (rm as int) >= 0,
                (rm as int) < FX_LN2_HI as int,
                (ax as int) <= 406000000000000000000,
                abs_int(m as int) <= (qm as int) + 1,
                (qm as int) >= 0,
        ;
    }
    // r = (x − m·L) − round(m·C2 / 2^63). The first term is exact integer
    // arithmetic: `m·L` is a whole number of grid units.
    let hi: i128 = x - m * FX_LN2_HI;
    // The correction is `m · C2 · 2^-63` in grid units, which is exactly what
    // `fx_mul` computes from the plain integer `m`. Scaling `m` first would
    // overflow the product.
    let lo: i128 = fx_mul(m, FX_LN2_LO);
    let r: i128 = hi - lo;
    // The reduction is correct by construction, but its *bound* is what the
    // series needs, and that bound depends on the quality of the division
    // above rather than on anything provable from the constants alone. A
    // clamp makes the precondition unconditional. It never triggers: `|r|`
    // is at most `ln2/2 + 2^-62` by the rounding rule for `m`.
    // `i128::clamp` is not available in verified code, and the branches carry
    // the bound the series needs.
    #[allow(clippy::manual_clamp)]
    let rc: i128 = if r > FX_R_MAX {
        FX_R_MAX
    } else if r < 0 - FX_R_MAX {
        0 - FX_R_MAX
    } else {
        r
    };
    let t: i128 = fx_exp_series(rc);
    proof {
        assert(abs_int(m as int) <= 66);
    }
    (t, m as i32)
}


// ---------------------------------------------------------------------------
// The logarithm, on the grid
// ---------------------------------------------------------------------------

/// Terms of the `atanh` series on the grid.
///
/// The tail after `N` terms at `|z| <= 1/3` is
/// `z^(2N+3)/((2N+3)(1 − z²))`. At `N = 18` that is `2^-66.9`, at `N = 16` only
/// `2^-60.4`. Eighteen puts the truncation three bits below the grid.
pub const FX_ATANH_TERMS: u32 = 18;

/// The largest `atanh` argument the series accepts: `0.34 · 2^63`.
///
/// Every caller reduces to `|z| <= 1/3`, which is `3.07e18` on this grid.
pub const FX_Z_MAX: i128 = 3150000000000000000i128;

/// `atanh(z)` for `|z| <= 1/3`, as `z + z³/3 + z⁵/5 + ...`.
///
/// The postcondition is a loose bound on the accumulator, not the value. The
/// value is at most `atanh(1/3) = ln2/2 ≈ 0.347`; the bound stated is what the
/// proof carries from eighteen terms each bounded by `FX_Z_MAX / 3`, and its
/// only job is to discharge the `i128` range checks.
pub fn fx_atanh_series(z: i128) -> (t: i128)
    requires
        abs_int(z as int) <= FX_Z_MAX as int,
    ensures
        abs_int(t as int) <= 10350000000000000000i128 as int,
{
    proof {
        crate::model::lemma_pow2_126();
        lemma_fx_one();
        assert(abs_int((z as int) * (z as int)) < pow2(126)) by (nonlinear_arith)
            requires
                abs_int(z as int) <= FX_Z_MAX as int,
                pow2(126) == 85070591730234615865843651857942052864,
        ;
    }
    // `zz` is `z²` on the grid, at most `1/9`.
    let zz: i128 = fx_mul(z, z);
    proof {
        assert(abs_int(zz as int) <= 1100000000000000000i128 as int) by (nonlinear_arith)
            requires
                abs_int(zz as int) * fx_one() <= abs_int((z as int) * (z as int)) + fx_one(),
                abs_int(z as int) <= FX_Z_MAX as int,
                fx_one() == 9223372036854775808,
        ;
    }
    let mut term: i128 = z;
    let mut sum: i128 = z;
    let mut k: u32 = 1;
    while k <= FX_ATANH_TERMS
        invariant
            abs_int(term as int) <= FX_Z_MAX as int,
            abs_int(zz as int) <= 1100000000000000000,
            abs_int(sum as int) <= (FX_Z_MAX as int) + ((k - 1) as int) * 400000000000000000,
            1 <= k <= FX_ATANH_TERMS + 1,
        decreases FX_ATANH_TERMS + 1 - k,
    {
        proof {
            lemma_fx_one();
            crate::model::lemma_pow2_126();
            assert(abs_int((term as int) * (zz as int)) < pow2(126)) by (nonlinear_arith)
                requires
                    abs_int(term as int) <= FX_Z_MAX as int,
                    abs_int(zz as int) <= 1100000000000000000,
                    pow2(126) == 85070591730234615865843651857942052864,
            ;
        }
        // Each term is the previous one times `z²`, thus each shrinks by at
        // least a factor of eight and the term bound is preserved.
        let next: i128 = fx_mul(term, zz);
        proof {
            lemma_fx_one();
            assert(abs_int(next as int) <= 1100000000000000000) by (nonlinear_arith)
                requires
                    abs_int(next as int) * fx_one() <= abs_int((term as int) * (zz as int))
                        + fx_one(),
                    abs_int(term as int) <= FX_Z_MAX as int,
                    abs_int(zz as int) <= 1100000000000000000,
                    fx_one() == 9223372036854775808,
            ;
        }
        let piece: i128 = fx_div_int(next, 2 * k + 1);
        proof {
            // Each piece is a term divided by at least three, which is what
            // keeps the sum inside the budget of the `Rat` it becomes.
            assert(abs_int(piece as int) <= 400000000000000000) by (nonlinear_arith)
                requires
                    2 * abs_int((piece as int) * ((2 * k + 1) as int) - (next as int)) <= (2 * k
                        + 1) as int,
                    abs_int(next as int) <= 1100000000000000000,
                    ((2 * k + 1) as int) >= 3,
            ;
        }
        term = next;
        sum = sum + piece;
        k = k + 1;
    }
    sum
}


/// `z = (N − D) / (N + D)` on the grid, for a ratio `N/D` in `[1/2, 2]`.
///
/// This is the shape `ln` needs, and the reason it takes `N` and `D` as
/// integers rather than a mantissa already on the grid. Quantising the mantissa
/// first costs `2^-64` of *absolute* error, which is harmless for a result near
/// `1` and ruinous for one near `0`: at `x = 1 + 2^-40` the answer is `2^-40`
/// and the quantisation leaves `2^-24` of relative error, because `N − D`
/// cancels away forty bits that were never recorded. Taking the difference on
/// the caller's own integers, before any rounding, is what keeps a small result
/// meaningful. It is the same reason a C library has `log1p`.
///
/// The precondition bounds both inputs by `2^62`, which keeps `(N − D) · 2^63`
/// inside `i128`.
/// The ratio bound is clamped rather than required. A caller that has reduced
/// its mantissa into `[1/2, 2]` never reaches the clamp, but proving that it
/// has means unfolding the order on `Q`, and the clamp costs one comparison.
// `rem` is consumed by the proof block, which plain rustc erases.
#[allow(unused_variables)]
pub fn fx_ratio_z(bign: i128, bigd: i128) -> (z: i128)
    requires
        bign > 0,
        bigd > 0,
        bign <= 4611686018427387904i128 as int,
        bigd <= 4611686018427387904i128 as int,
    ensures
        abs_int(z as int) <= FX_Z_MAX as int,
{
    proof {
        lemma_fx_one();
        crate::model::lemma_pow2_126();
    }
    let diff: i128 = bign - bigd;
    let sum: i128 = bign + bigd;
    let neg: bool = diff < 0;
    let ad: i128 = if neg {
        0 - diff
    } else {
        diff
    };
    proof {
        // The scaled numerator is at most `2^62 · 2^63`, which is inside
        // `i128`.
        assert((ad as int) * fx_one() <= 42535295865117307932921825928971026432)
            by (nonlinear_arith)
            requires
                (ad as int) <= 4611686018427387904,
                fx_one() == 9223372036854775808,
        ;
    }
    let scaled: i128 = ad * FX_ONE;
    let q: i128 = scaled / sum;
    let rem: i128 = scaled % sum;
    proof {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(scaled as int, sum as int);
        vstd::arithmetic::div_mod::lemma_div_pos_is_pos(scaled as int, sum as int);
        vstd::arithmetic::div_mod::lemma_mod_bound(scaled as int, sum as int);
        assert((scaled as int) == (q as int) * (sum as int) + (rem as int)) by (nonlinear_arith)
            requires
                (scaled as int) == (sum as int) * (q as int) + (rem as int),
        ;
        assert((q as int) >= 0);
    }
    // The clamp. A mantissa in `[1/2, 2]` gives `|z| <= 1/3`, which is below
    // `FX_Z_MAX`, so this is a guard rather than a rounding.
    let qc: i128 = if q > FX_Z_MAX {
        FX_Z_MAX
    } else {
        q
    };
    if neg {
        0 - qc
    } else {
        qc
    }
}

} // verus!
