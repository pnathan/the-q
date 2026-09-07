//! Fixed-point kernel for `exp` and `ln`.
//!
//! Values are `i128` on a `2^-63` grid (`V` denotes `V · 2^-63`), two guard
//! bits finer than the crate's `2^-61` grid, so a series can accumulate
//! rounding error here and be regridded once at the end. A multiply is one
//! `i128` product and one shift-and-round, with no gcd or canonical form; that
//! is why `exp` and `ln` cost under two microseconds where the `Q`-series
//! functions cost tens.
//!
//! Proven: each operation's rounding error against the exact product or
//! quotient, and the absence of overflow (every function states the input
//! range that discharges it; [`fx_mul`] needs `|a · b| < 2^126`). Not proven:
//! that a truncated series approximates its function.

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

/// The product on the grid: `|r · 2^63 − a · b| <= 2^62`, nearest with ties
/// away from zero (symmetric under negation). The precondition on the product
/// discharges the overflow check.
/// Public only because Verus's visibility rules require it; not part of the
/// crate's semver-stable API.
///
/// ```
/// use the_q::fx::{fx_mul, FX_ONE};
///
/// // 1.0 * 0.5 == 0.5, exactly, on the grid.
/// assert_eq!(fx_mul(FX_ONE, FX_ONE / 2), FX_ONE / 2);
/// ```
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

/// `v / k` on the grid for a small integer `k`: `|r · k − v| <= k / 2`.
/// Public only because Verus's visibility rules require it; not part of the
/// crate's semver-stable API.
///
/// ```
/// use the_q::fx::{fx_div_int, FX_ONE};
///
/// // 1.0 / 2 == 0.5, exactly.
/// assert_eq!(fx_div_int(FX_ONE, 2), FX_ONE / 2);
/// ```
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

/// Bound on the Horner accumulator, `1.6 · 2^63`; keeps [`fx_mul`]'s product
/// under `2^126`.
pub const FX_T_MAX: i128 = 14757395258967641292i128;

/// Terms in the exponential series: the tail at `|z| <= 0.3536` is `2^-73.8`
/// after 16 terms, a term of margin below the grid.
pub const FX_EXP_TERMS: u32 = 16;

/// `e^z` for a reduced `z`, by Horner: `T := 1 + (z/k)·T` for `k` from
/// [`FX_EXP_TERMS`] down to 1. The postcondition is the accumulator bound that
/// discharges the overflow checks; distance to `e^z` is measured, not stated.
/// Public only because Verus's visibility rules require it; not part of the
/// crate's semver-stable API.
///
/// ```
/// use the_q::fx::{fx_exp_series, FX_ONE};
///
/// // e^0 == 1.0, exactly.
/// assert_eq!(fx_exp_series(0), FX_ONE);
/// ```
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

/// Second word of `ln 2`, `round((ln2 · 2^63 − FX_LN2_HI) · 2^63)`; the pair
/// holds `ln 2` to `2^-128.4`, so `m · ln2` with `m <= 64` is exact enough.
pub const FX_LN2_LO: i128 = -974768846722515540i128;

/// `e^x` on the grid as `(t, m)` denoting `t · 2^(m − 63)`. Cody-Waite:
/// `m = nearest(x / ln2)`, `r = x − m·ln2` with `ln 2` in two words (exact to
/// `2^-128`), series on `|r| <= ln2/2`, and `2^m` is an exponent adjustment.
/// Public only because Verus's visibility rules require it; not part of the
/// crate's semver-stable API.
///
/// ```
/// use the_q::fx::{fx_exp_reduced, FX_ONE};
///
/// // e^0 == 1.0 * 2^(0 - 63), i.e. m == 0 and t == FX_ONE.
/// assert_eq!(fx_exp_reduced(0), (FX_ONE, 0));
/// ```
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
    // The clamp never triggers (`|r| <= ln2/2 + 2^-62`) and makes the series'
    // precondition unconditional; `i128::clamp` is unavailable in verified code.
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

/// `atanh(z)` for `|z| <= 1/3`. The postcondition bounds the accumulator only,
/// to discharge the range checks.
/// Public only because Verus's visibility rules require it; not part of the
/// crate's semver-stable API.
///
/// ```
/// use the_q::fx::fx_atanh_series;
///
/// // atanh(0) == 0.
/// assert_eq!(fx_atanh_series(0), 0);
/// ```
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


/// `z = (N − D) / (N + D)` on the grid for `N/D` in `[1/2, 2]`, taken on the
/// caller's integers so that `N − D` is exact (the `log1p` reason: quantising
/// first loses the cancelled bits). Inputs below `2^62`; the ratio is clamped
/// rather than required.
/// Public only because Verus's visibility rules require it; not part of the
/// crate's semver-stable API.
///
/// ```
/// use the_q::fx::fx_ratio_z;
///
/// // N == D gives z == 0.
/// assert_eq!(fx_ratio_z(5, 5), 0);
/// ```
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
