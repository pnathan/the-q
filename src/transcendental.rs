//! Transcendental and root functions on the extended [`Q`].
//!
//! # These functions are not rational-closed
//!
//! `sqrt(2)`, `exp(1)` and `sin(1)` are irrational. No rational type can return
//! them. This module returns the nearest representable rational to the true
//! value, with a stated error bound. This is the same contract that the
//! arithmetic makes, applied to functions that have no exact answer.
//!
//! # Termination is structural
//!
//! Each iteration runs a fixed number of steps. No iteration loops until a
//! convergence test passes. A fixed count terminates trivially, which lets
//! Verus discharge these functions. A fixed count also makes the cost of each
//! call constant and predictable. The counts are large enough for the iteration
//! to converge to within the representable grid.
//!
//! # Sources of error
//!
//! There are two independent sources:
//!
//! * Truncation. The series or the iteration stops after a fixed number of
//!   terms. The term count keeps the tail below the grid resolution.
//! * Rounding. Each intermediate `Q` operation rounds and adds at most
//!   `2^-61 · max(1, |value|)`. Over `k` operations these errors accumulate
//!   additively, as the V8 bound in `nary` states.
//!
//! Rounding is the larger source. Thus these functions are accurate to
//! approximately `2^-55`, and not to the `2^-61` of a single operation. This
//! accuracy is better than the `2^-53` of `f64`.
//!
//! # Precision decreases for results far below 1
//!
//! The R3 error bound is `2^-61 · max(1, |exact|)`. Below 1 this bound is
//! absolute, not relative. A value near `1` thus carries approximately 61
//! significant bits, but a value near `2^-43` carries approximately 18. The
//! grid spacing is constant, so a small value has fewer grid points relative to
//! its own magnitude.
//!
//! The effect is largest when the output of a function is small. `exp(-30)` is
//! approximately `2^-43`, thus its relative accuracy is approximately `2^-18`.
//! `ln(exp(-30))` differs from `-30` by approximately `5e-6`. The test
//! `ln_inverts_exp_to_the_precision_the_grid_allows` measures this difference
//! at `2^-20`. The cause is the intermediate value, which cannot carry the
//! information.
//!
//! If small values are important, scale the problem so that the values are not
//! small. The budget is larger near `1` than near `0`.
//!
//! # Failure is a value, not a panic
//!
//! Each function is total. `sqrt` of a negative number is `Nan`. `ln(0)` is
//! `NegInf`. An argument whose result is not representable gives a saturated
//! result. The special-value results come from the §2 denotations in issue #26,
//! as the arithmetic tables do. A result is sound only if its denotation
//! contains the true image of the denotation of the operand.
//!
//! One result of that rule is important: `sqrt` of a saturated value is `Nan`,
//! and not `PosSat`. `PosSat` denotes `(MAX_MAG, ∞)`. The image of that
//! interval under `sqrt` is `(2^31, ∞)`, which extends far below `MAX_MAG` and
//! thus contains representable values. A `PosSat` result would claim a
//! magnitude that the value can fail to have. The same rule makes `ln(PosSat)`
//! and `atan(PosSat)` `Nan`.

use verus_builtin_macros::verus;

#[allow(unused_imports)]
use verus_builtin::*;
#[allow(unused_imports)]
use vstd::prelude::*;

use crate::ext::Q;
use crate::types::Rat;

verus! {

/// Integer square root: the largest `r >= 0` with `r*r <= n`.
///
/// The function uses Newton's method on integers. Each step decreases the
/// estimate until the estimate settles. The `decreases` clause uses that
/// property. The classic formulation loops `while y < x`, and that guard is the
/// same "still decreasing" test.
///
/// For `n < 0` the function returns `0` and does not panic. No caller in this
/// crate passes a negative argument, and a total function is easier to reason
/// about than a guarded one.
///
/// The postcondition is the defining property of an integer square root, and
/// not a bound on it: `r*r <= n < (r+1)*(r+1)` pins `r` to one value. A weaker
/// postcondition such as `r >= 0 && r <= n` also holds for wrong answers, for
/// example `isqrt(2) == 2`, and thus verifies against a defective
/// implementation.
///
/// The implementation runs Newton's method for speed, then a bounded
/// correction. Newton's method alone reaches the answer, but a proof of that
/// property needs AM-GM reasoning over integer division. The correction loops
/// establish the postcondition directly from their own exit conditions. In
/// practice each loop runs at most one time and costs two `i128`
/// multiplications.
pub fn isqrt_i64(n: i64) -> (r: i64)
    requires
        // Every caller passes a `Rat` component, which the type invariant
        // already bounds by `MAX_MAG`. The bound is load-bearing rather than
        // decorative: it is what keeps `x + n/x` inside `i64`, since that sum
        // is at most `2n` and `2 · MAX_MAG == i64::MAX - 1`.
        0 <= n <= crate::types::MAX_MAG,
    ensures
        r >= 0,
        (r as int) * (r as int) <= n as int,
        ((r as int) + 1) * ((r as int) + 1) > n as int,
{
    if n < 2 {
        proof {
            // `n` is 0 or 1, and both are their own integer square root.
            assert((n as int) * (n as int) <= n as int) by (nonlinear_arith)
                requires
                    0 <= n as int <= 1,
            ;
            assert(((n as int) + 1) * ((n as int) + 1) > n as int) by (nonlinear_arith)
                requires
                    0 <= n as int <= 1,
            ;
        }
        return n;
    }
    let mut x: i64 = n;
    // `(n + 1) / 2`, *not* `n / 2 + 1` — see the note above.
    let mut y: i64 = (n + 1) / 2;
    // `y < x` is the decreasing test; `x` is the measure.
    while y < x
        invariant
            x >= 1,
            y >= 1,
            x <= n,
            n <= crate::types::MAX_MAG,
        decreases x,
    {
        x = y;
        proof {
            // `1 <= x <= n` gives `n/x >= n/n == 1`, which is what keeps the
            // next estimate positive. Integer division does not give the
            // prover this for free.
            vstd::arithmetic::div_mod::lemma_div_is_ordered_by_denominator(
                n as int,
                x as int,
                n as int,
            );
            vstd::arithmetic::div_mod::lemma_div_by_self(n as int);
        }
        // `x <= n` and `n / x <= n`, so the sum is at most `2n <= 2 · MAX_MAG`,
        // which is `i64::MAX - 1`.
        y = (x + n / x) / 2;
    }
    // Correction, in `i128` so the squares cannot overflow: `r <= n <= 2^62`
    // gives `r*r <= 2^124`.
    let mut r: i64 = x;
    // The squares are in variables and not in the loop guards, for two reasons.
    // First, `r*r` fits `i128` only as a nonlinear fact, which the prover
    // reaches only in a proof block. Second, the negation of a `while` guard
    // carries the postcondition out of the loop, and a `loop`/`break` form
    // discards that negation.
    proof {
        assert(0 <= (r as int) * (r as int) <= (crate::types::MAX_MAG as int) * (crate::types::MAX_MAG as int))
            by (nonlinear_arith)
            requires
                0 <= r as int <= crate::types::MAX_MAG as int,
        ;
    }
    let mut sq: i128 = (r as i128) * (r as i128);
    while r > 0 && sq > n as i128
        invariant
            0 <= r <= n,
            2 <= n <= crate::types::MAX_MAG,
            sq as int == (r as int) * (r as int),
        decreases r,
    {
        r = r - 1;
        proof {
            assert(0 <= (r as int) * (r as int) <= (crate::types::MAX_MAG as int) * (crate::types::MAX_MAG as int))
                by (nonlinear_arith)
                requires
                    0 <= r as int <= crate::types::MAX_MAG as int,
            ;
        }
        sq = (r as i128) * (r as i128);
    }
    proof {
        // Exiting means `r == 0` or `r*r <= n`, and `0*0 == 0 <= n`, so the
        // defining lower bound holds either way.
        assert((r as int) * (r as int) <= n as int) by (nonlinear_arith)
            requires
                0 <= r as int,
                2 <= n as int,
                r as int == 0 || (r as int) * (r as int) <= n as int,
        ;
    }
    proof {
        assert(0 <= ((r as int) + 1) * ((r as int) + 1) <= ((crate::types::MAX_MAG as int) + 1) * (
        (crate::types::MAX_MAG as int) + 1)) by (nonlinear_arith)
            requires
                0 <= r as int <= crate::types::MAX_MAG as int,
        ;
    }
    let mut nxt: i128 = ((r as i128) + 1) * ((r as i128) + 1);
    while nxt <= n as i128
        invariant
            0 <= r <= n,
            2 <= n <= crate::types::MAX_MAG,
            (r as int) * (r as int) <= n as int,
            nxt as int == ((r as int) + 1) * ((r as int) + 1),
        decreases n - r,
    {
        proof {
            // `(r+1)^2 <= n` with `r >= 0` forces `r + 1 <= n`, which keeps the
            // measure decreasing and `r` inside the budget.
            assert((r as int) + 1 <= n as int) by (nonlinear_arith)
                requires
                    0 <= r as int,
                    ((r as int) + 1) * ((r as int) + 1) <= n as int,
            ;
        }
        r = r + 1;
        proof {
            assert(0 <= ((r as int) + 1) * ((r as int) + 1) <= ((crate::types::MAX_MAG as int) + 1) * (
            (crate::types::MAX_MAG as int) + 1)) by (nonlinear_arith)
                requires
                    0 <= r as int <= crate::types::MAX_MAG as int,
            ;
        }
        nxt = ((r as i128) + 1) * ((r as i128) + 1);
    }
    r
}

/// **`isqrt`'s contract pins its answer**: any two non-negative integers
/// satisfying `r·r <= n < (r+1)·(r+1)` for the same `n` are equal.
///
/// This is the categoricity proof for the `isqrt` specification. A weaker
/// contract such as `0 <= r <= n` holds for more than one value. This theorem
/// states that the specification in use holds for exactly one value, which is
/// the true floor of the square root.
pub proof fn theorem_isqrt_unique(n: int, r1: int, r2: int)
    requires
        0 <= r1,
        r1 * r1 <= n,
        n < (r1 + 1) * (r1 + 1),
        0 <= r2,
        r2 * r2 <= n,
        n < (r2 + 1) * (r2 + 1),
    ensures
        r1 == r2,
{
    // If the roots differed, the smaller one's successor square would be
    // trapped: (r1+1)^2 <= r2^2 <= n contradicts n < (r1+1)^2.
    if r1 < r2 {
        assert((r1 + 1) * (r1 + 1) <= r2 * r2) by (nonlinear_arith)
            requires
                0 <= r1 + 1,
                r1 + 1 <= r2,
        ;
    }
    if r2 < r1 {
        assert((r2 + 1) * (r2 + 1) <= r1 * r1) by (nonlinear_arith)
            requires
                0 <= r2 + 1,
                r2 + 1 <= r1,
        ;
    }
}

/// **`isqrt` is monotone**: a larger radicand cannot have a smaller integer
/// square root.
///
/// The theorem speaks about the contract and not about the code: results that
/// satisfy the specification for `n1 <= n2` are ordered. It thus applies at
/// each call site. It also permits componentwise reasoning about the quality of
/// `sqrt_seed`: a larger numerator gives a seed numerator that is not smaller,
/// independently of the later Newton refinement.
pub proof fn theorem_isqrt_monotone(n1: int, n2: int, r1: int, r2: int)
    requires
        n1 <= n2,
        0 <= r1,
        r1 * r1 <= n1,
        n1 < (r1 + 1) * (r1 + 1),
        0 <= r2,
        r2 * r2 <= n2,
        n2 < (r2 + 1) * (r2 + 1),
    ensures
        r1 <= r2,
{
    // Otherwise n2 < (r2+1)^2 <= r1^2 <= n1 <= n2.
    if r2 < r1 {
        assert((r2 + 1) * (r2 + 1) <= r1 * r1) by (nonlinear_arith)
            requires
                0 <= r2 + 1,
                r2 + 1 <= r1,
        ;
    }
}

/// **`isqrt` inverts squaring exactly**: on a perfect square `k·k` the
/// contract forces the answer `k`.
///
/// Perfect squares are the one input family where the floor and the true square
/// root are equal, thus the nearest grid point is the exact value. The proof is
/// not an unfolding of the contract. It uses the nonlinear fact
/// `k·k < (k+1)·(k+1)` together with categoricity to fix the result at `k`.
pub proof fn theorem_isqrt_of_square(k: int, r: int)
    requires
        0 <= k,
        0 <= r,
        r * r <= k * k,
        k * k < (r + 1) * (r + 1),
    ensures
        r == k,
{
    // k itself satisfies the contract for n == k·k...
    assert(k * k < (k + 1) * (k + 1)) by (nonlinear_arith)
        requires
            0 <= k,
    ;
    // ...and the contract pins its answer.
    theorem_isqrt_unique(k * k, r, k);
}

/// A first approximation to `sqrt(num/den)`, as a `Q`.
///
/// `isqrt(num) / isqrt(den)` is within a factor of two of the true root, which
/// is close enough that six Newton steps reach the grid. Starting from `x`
/// itself would need about thirty, and every extra step is another rounding.
fn sqrt_seed(x: Rat) -> (r: Q)
    requires
        x.wf(),
        x.n() > 0,
    ensures
        r.wf(),
{
    let rn = isqrt_i64(x.numerator());
    let rd = isqrt_i64(x.denominator());
    // `isqrt` of a positive value is at least 1, so this denominator is safe;
    // `Q::new` is total regardless.
    Q::new(if rn < 1 {
        1
    } else {
        rn
    }, if rd < 1 {
        1
    } else {
        rd
    })
}

impl Q {
    /// The non-negative square root.
    ///
    /// | operand | result | why |
    /// |---|---|---|
    /// | `Number(x)`, `x > 0` | nearest representable root | Newton |
    /// | `Number(0)` | `Number(0)` | exact |
    /// | `Number(x)`, `x < 0` | `Nan` | no real root |
    /// | `PosSat` | `Nan` | image `(2^31, ∞)` reaches below `MAX_MAG` |
    /// | `NegSat` | `Nan` | negative |
    /// | `PosInf` | `PosInf` | exact |
    /// | `NegInf` | `Nan` | negative |
    /// | `Nan` | `Nan` | |
    ///
    /// The Newton iteration `y <- (y + x/y)/2` converges quadratically. From
    /// the integer-root seed, seven steps are more than sufficient: a further
    /// step cannot change the rounded answer.
    pub fn sqrt(self) -> (r: Q)
        requires
            self.wf(),
        ensures
            r.wf(),
            self.spec_is_nan() ==> r.spec_is_nan(),
            self.spec_is_zero() ==> r.spec_is_zero(),
    {
        match self {
            Q::Number(x) => {
                let s = x.signum();
                if s < 0 {
                    Q::Nan
                } else if s == 0 {
                    Q::zero()
                } else {
                    let two = Q::new(2, 1);
                    let mut y = sqrt_seed(x);
                    let q = Q::Number(x);
                    let mut i: u32 = 0;
                    while i < SQRT_ITERS
                        invariant
                            y.wf(),
                            q.wf(),
                            two.wf(),
                            i <= SQRT_ITERS,
                        decreases SQRT_ITERS - i,
                    {
                        // y <- (y + x/y) / 2. A zero or special `y` gives a
                        // division that reports the state and does not trap.
                        // The result stays a value.
                        y = Q::div(Q::add(y, Q::div(q, y)), two);
                        i = i + 1;
                    }
                    y
                }
            },
            // The image of (MAX_MAG, inf) under sqrt is (2^31, inf), which
            // extends far below MAX_MAG. No saturation state is thus sound.
            Q::PosSat => Q::Nan,
            Q::NegSat => Q::Nan,
            Q::PosInf => Q::PosInf,
            Q::NegInf => Q::Nan,
            Q::Nan => Q::Nan,
        }
    }
}

// ---------------------------------------------------------------------------
// Series lengths
//
// Each series has its own count. The count comes from the tail bound of that
// series against the grid resolution `2^-61`, which is approximately
// `4.34e-19`. A shared count is wrong in two directions at the same time. It is
// too short for `atan`, whose coefficients are `1/(2k+1)`. It is almost twice
// the necessary length for `sin`, whose coefficients are `1/(2k+1)!`.
//
// Each count is a constant and does not come from a convergence test. Thus
// termination is structural and the cost of a call is constant.
// ---------------------------------------------------------------------------

/// Terms of the `atanh` series, whose argument is reduced to `|z| <= 1/3`.
///
/// The tail at `k` is `3^-(2k+1)/(2k+1)`; `k = 18` gives `6.0e-20`, under the
/// grid, while `k = 17` gives `5.7e-19`, over it. The loop covers `k` up to
/// `SERIES_TERMS - 1 = 19`, one past what is needed.
const SERIES_TERMS: u32 = 20;


/// Terms of the `sin` and `cos` series, whose argument is reduced to
/// `|z| <= π/4`.
///
/// The tail at `k` is `(π/4)^(2k+1)/(2k+1)!`; `k = 9` gives `8.4e-20`, under
/// the grid, while `k = 8` gives `4.6e-17`, well over it. The loop covers `k`
/// up to `TRIG_TERMS - 1 = 10`.
///
/// A dedicated count is most valuable here. The factorial denominators make
/// this series converge much faster than the `atan` series. The `atan` length
/// thus doubles the cost of each `sin` and `cos` call and adds no accuracy.
const TRIG_TERMS: u32 = 11;

/// Newton iterations in [`Q::sqrt`].
///
/// The integer-root seed is within a factor of two, so the initial relative
/// error is at most about `1/2`. Newton squares it each step:
/// `0.5 → 0.125 → 7.8e-3 → 3.1e-5 → 4.6e-10 → 1.1e-19`. The sixth step is thus
/// below the grid. Seven steps give a margin. An eighth step adds no accuracy.
const SQRT_ITERS: u32 = 7;


/// Beyond `|x| > 44`, `exp(x)` leaves the budget in one direction or the other:
/// `exp(44) > 2^63` and `exp(-44) < 2^-63`. Both are decided without summing
/// anything.
const EXP_ARG_LIMIT: i64 = 44;


/// A `Rat` on the fixed-point grid: `round(num · 2^63 / den)`.
///
/// The receiver's magnitude is at most `EXP_ARG_LIMIT`, thus the result is at
/// most `44 · 2^63`, which is what [`crate::fx::fx_exp_reduced`] accepts. The
/// scaled numerator is at most `2^62 · 2^63 = 2^125` and fits `i128`.
// `rem` is consumed by the proof block, which plain rustc erases.
#[allow(unused_variables)]
fn fx_to_grid(x: Rat) -> (r: i128)
    requires
        x.wf(),
        crate::model::abs_int(x.n()) <= (EXP_ARG_LIMIT as int) * x.d(),
    ensures
        crate::model::abs_int(r as int) <= 406000000000000000000i128 as int,
{
    proof {
        crate::model::lemma_max_mag_pow2();
        crate::model::lemma_pow2_125();
        crate::model::lemma_pow2_63();
        assert(crate::model::abs_int((x.n()) * (crate::fx::FX_ONE as int)) <= 406000000000000000000
            * (x.d())) by (nonlinear_arith)
            requires
                crate::model::abs_int(x.n()) <= (EXP_ARG_LIMIT as int) * x.d(),
                x.d() > 0,
                (crate::fx::FX_ONE as int) == 9223372036854775808,
                (EXP_ARG_LIMIT as int) == 44,
        ;
    }
    let scaled: i128 = (x.num as i128) * crate::fx::FX_ONE;
    let d: i128 = x.den as i128;
    let neg: bool = scaled < 0;
    let m: i128 = if neg {
        0 - scaled
    } else {
        scaled
    };
    let q: i128 = m / d;
    let rem: i128 = m % d;
    proof {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(m as int, d as int);
        vstd::arithmetic::div_mod::lemma_div_pos_is_pos(m as int, d as int);
        vstd::arithmetic::div_mod::lemma_mod_bound(m as int, d as int);
        assert((m as int) == (q as int) * (d as int) + (rem as int)) by (nonlinear_arith)
            requires
                (m as int) == (d as int) * (q as int) + (rem as int),
        ;
        assert((q as int) <= 406000000000000000000) by (nonlinear_arith)
            requires
                (m as int) == (q as int) * (d as int) + (rem as int),
                (rem as int) >= 0,
                (d as int) >= 1,
                (m as int) <= 406000000000000000000 * (d as int),
        ;
    }
    if neg {
        0 - q
    } else {
        q
    }
}

/// `t / 4`, rounded, which brings the fixed-point mantissa inside `i64`.
///
/// The mantissa is at most `1.6 · 2^63`. A quarter of that is `1.6 · 2^61`,
/// which is below `MAX_MAG`, and the denominator becomes `2^61`.
fn fx_quarter(t: i128) -> (r: i64)
    requires
        crate::model::abs_int(t as int) <= crate::fx::FX_T_MAX as int,
    ensures
        crate::model::abs_int(r as int) <= crate::model::max_mag(),
{
    proof {
        crate::model::lemma_max_mag_pow2();
    }
    let neg: bool = t < 0;
    let m: i128 = if neg {
        0 - t
    } else {
        t
    };
    let q: i128 = (m + 2) / 4;
    proof {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod((m as int) + 2, 4int);
        vstd::arithmetic::div_mod::lemma_mod_bound((m as int) + 2, 4int);
        assert((q as int) <= crate::model::max_mag()) by (nonlinear_arith)
            requires
                ((m as int) + 2) == 4 * (q as int) + (((m as int) + 2) % 4),
                (((m as int) + 2) % 4) >= 0,
                (m as int) <= 14757395258967641292,
                crate::model::max_mag() == 4611686018427387903,
        ;
    }
    if neg {
        (0 - q) as i64
    } else {
        q as i64
    }
}

/// `2^m` as a `Q`, saturating where the exponent leaves the budget.
///
/// `|m| <= 66`, and `2^62` is already past `MAX_MAG`, thus an exponent at or
/// above `62` saturates and one at or below `-62` underflows to zero. Both are
/// the same answers the argument limit gives for `exp` itself.
fn pow2_q(m: i32) -> (r: Q)
    ensures
        r.wf(),
{
    if m >= 62 {
        Q::PosSat
    } else if m <= -62 {
        Q::zero()
    } else if m >= 0 {
        Q::new(1i64 << (m as u32), 1)
    } else {
        Q::new(1, 1i64 << ((0 - m) as u32))
    }
}

impl Q {
    /// `e^self`.
    ///
    /// | operand | result | why |
    /// |---|---|---|
    /// | `Number(x)`, `x > 44` | `PosSat` | `exp(44) > MAX_MAG` |
    /// | `Number(x)`, `x < -44` | `Number(0)` | underflow, and §11 places that inside R3 |
    /// | `Number(x)` otherwise | series | |
    /// | `PosSat` | `PosSat` | image `(exp(MAX_MAG), ∞) ⊆ (MAX_MAG, ∞)` |
    /// | `NegSat` | `Nan` | see below |
    /// | `PosInf` | `PosInf` | |
    /// | `NegInf` | `Number(0)` | exact limit |
    /// | `Nan` | `Nan` | |
    ///
    /// `exp(NegSat)` is `Nan` and not zero. The difference from
    /// `exp(Number(-50))` is intentional. The image of `(-∞, -MAX_MAG)` is
    /// `(0, exp(-MAX_MAG))`, and that interval does not contain zero. A
    /// `Number(0)` result is thus unsound, because it asserts an exact value
    /// that the true result does not have. For a `Number` argument the rounding
    /// contract applies instead, and underflow to zero is inside that contract
    /// (#26 §11). Section 11 makes the same decision for `recip(Sat)`: option
    /// (A) does not continue a computation past an overflow.
    ///
    /// # Method
    ///
    /// The method is `exp(x) = exp(x / 2^k)^(2^k)`. The function selects the
    /// smallest `k` that brings `|x|` to at most `1/2`, then sums twenty
    /// Maclaurin terms, then applies `k` squarings. `k` is adaptive and not
    /// constant, because each squaring doubles the relative error. A constant
    /// `k = 8` costs each small argument a factor of 256 in accuracy.
    pub fn exp(self) -> (r: Q)
        requires
            self.wf(),
        ensures
            r.wf(),
            self.spec_is_nan() ==> r.spec_is_nan(),
    {
        match self {
            Q::PosSat => Q::PosSat,
            Q::NegSat => Q::Nan,
            Q::PosInf => Q::PosInf,
            Q::NegInf => Q::zero(),
            Q::Nan => Q::Nan,
            Q::Number(x) => {
                // The argument limit, tested on the components rather than
                // through the order. The conversion below needs the bound in
                // exactly this form, and `|num| <= 44 · den` *is* `|x| <= 44`
                // for a positive denominator.
                proof {
                    crate::model::lemma_max_mag_pow2();
                    assert(44int * x.d() <= 202914184810805067732) by (nonlinear_arith)
                        requires
                            x.d() <= 4611686018427387903,
                    ;
                }
                let lim: i128 = (EXP_ARG_LIMIT as i128) * (x.den as i128);
                let axn: i128 = if x.num < 0 {
                    0 - (x.num as i128)
                } else {
                    x.num as i128
                };
                if axn > lim {
                    return if x.num > 0 {
                        Q::PosSat
                    } else {
                        Q::zero()
                    };
                }
                // The argument on the fixed-point grid. `|x| <= 44` and
                // `x.den >= 1`, thus the scaled numerator is inside `i128`.
                let xg: i128 = fx_to_grid(x);
                let (t, m) = crate::fx::fx_exp_reduced(xg);
                // `t · 2^(m-63)`, assembled as a `Rat` times a power of two.
                // `t` is at most `1.6 · 2^63`, so a shift of two brings it
                // inside the budget with the denominator at `2^61`.
                let mant = Q::new(fx_quarter(t), 1i64 << 61);
                Q::mul(pow2_q(m), mant)
            },
        }
    }
}

/// Bound on the binary range reduction in [`Q::ln`].
///
/// Every representable value lies in `[1/MAX_MAG, MAX_MAG]`, and `MAX_MAG` is
/// below `2^62`, so sixty-three doublings or halvings always reach `[1/2, 2]`.
/// Sixty-four is carried for margin and makes the loops trivially terminating.
const MAX_BINARY_SHIFTS: u32 = 64;

/// `atanh(z) = z + z³/3 + z⁵/5 + …`, for `|z| <= 1/3`.
///
/// Each caller reduces its argument into that interval first. At `|z| = 1/3`
/// the twentieth odd term is `3^-39 / 39`, which is approximately `3e-21` and
/// thus below the `2^-61` grid. The truncation error is therefore not visible,
/// and the rounding error is the larger source. Each other series here has the
/// same balance.
fn atanh_series(z: Q) -> (r: Q)
    requires
        z.wf(),
    ensures
        r.wf(),
{
    let z2 = Q::mul(z, z);
    let mut term = z;
    let mut sum = z;
    let mut k: u32 = 1;
    while k < SERIES_TERMS
        invariant
            term.wf(),
            sum.wf(),
            z2.wf(),
            1 <= k <= SERIES_TERMS,
        decreases SERIES_TERMS - k,
    {
        term = Q::mul(term, z2);
        sum = Q::add(sum, Q::div(term, Q::new((2 * k + 1) as i64, 1)));
        k = k + 1;
    }
    sum
}

/// `e`, by the series `Σ 1/n!`.
///
/// This function is the derivation of [`e`]. It sums the series directly and
/// does not call `exp(1)`. The constant and the `exp` function are thus
/// independent, and a defect in the range reduction of `exp` cannot hide in
/// the value of `e`.
pub fn e_series() -> (r: Q)
    ensures
        r.wf(),
{
    let mut term = Q::one();
    let mut sum = Q::one();
    let mut i: u32 = 1;
    while i <= SERIES_TERMS
        invariant
            term.wf(),
            sum.wf(),
            1 <= i <= SERIES_TERMS + 1,
        decreases SERIES_TERMS + 1 - i,
    {
        term = Q::div(term, Q::new(i as i64, 1));
        sum = Q::add(sum, term);
        i = i + 1;
    }
    sum
}

/// `e`, the base of the natural logarithm.
///
/// The literal is the value that [`e_series`] computes. The test
/// `e_is_the_series_value` asserts that the two are bit-identical. See [`ln2`]
/// for the reason to use a checked literal instead of a series call.
pub fn e() -> (r: Q)
    ensures
        r.wf(),
{
    Q::new(3133965575612453543, 1152921504606846976)
}

/// `ln(2)`, by the series `2·atanh(1/3)`.
///
/// This function is the derivation of [`ln2`], which returns the same value as
/// a literal. Twenty series terms on each call dominate the cost of each
/// caller, thus [`ln2`] uses the literal.
pub fn ln2_series() -> (r: Q)
    ensures
        r.wf(),
{
    Q::mul(Q::new(2, 1), atanh_series(Q::new(1, 3)))
}

/// `ln(2)`.
///
/// The literal is the value that [`ln2_series`] computes. The test
/// `ln2_is_the_series_value` asserts that the two are bit-identical, thus the
/// constant is derived and checked. The test suite re-derives the value, and
/// the test fails if the series, the width budget or the rounding contract
/// changes.
pub fn ln2() -> (r: Q)
    ensures
        r.wf(),
{
    Q::new(399572145162582989, 576460752303423488)
}

impl Q {
    /// The natural logarithm.
    ///
    /// | operand | result | why |
    /// |---|---|---|
    /// | `Number(x)`, `x > 0` | series | |
    /// | `Number(0)` | `NegInf` | the exact limit |
    /// | `Number(x)`, `x < 0` | `Nan` | no real logarithm |
    /// | `PosSat` | `Nan` | image `(ln MAX_MAG, ∞) ≈ (43, ∞)` reaches below `MAX_MAG` |
    /// | `NegSat` | `Nan` | negative |
    /// | `PosInf` | `PosInf` | |
    /// | `NegInf` | `Nan` | negative |
    /// | `Nan` | `Nan` | |
    ///
    /// # Method
    ///
    /// The method has three steps. First, binary range reduction to
    /// `m ∈ [1/2, 2]`. Second, `ln(m) = 2·atanh((m-1)/(m+1))`, whose argument
    /// has a magnitude of at most `1/3`, which is the interval where the series
    /// is accurate. Third, `ln(x) = ln(m) + k·ln(2)`.
    ///
    /// The method uses the `atanh` form and not the direct `ln(1+u)` series.
    /// The terms of the `atanh` form are odd powers of a much smaller argument.
    /// For `m` at the end of the reduced range, `u` is `1`, and the direct
    /// series does not converge.
    pub fn ln(self) -> (r: Q)
        requires
            self.wf(),
        ensures
            r.wf(),
            self.spec_is_nan() ==> r.spec_is_nan(),
    {
        match self {
            Q::PosSat => Q::Nan,
            Q::NegSat => Q::Nan,
            Q::PosInf => Q::PosInf,
            Q::NegInf => Q::Nan,
            Q::Nan => Q::Nan,
            Q::Number(x) => {
                let s = x.signum();
                if s < 0 {
                    return Q::Nan;
                }
                if s == 0 {
                    return Q::NegInf;
                }
                let two = Q::new(2, 1);
                let half = Q::new(1, 2);
                let mut m = Q::Number(x);
                let mut up: u32 = 0;
                while up < MAX_BINARY_SHIFTS && Q::gt(m, two)
                    invariant
                        m.wf(),
                        two.wf(),
                        half.wf(),
                        up <= MAX_BINARY_SHIFTS,
                    decreases MAX_BINARY_SHIFTS - up,
                {
                    m = Q::div(m, two);
                    up = up + 1;
                }
                let mut down: u32 = 0;
                while down < MAX_BINARY_SHIFTS && Q::lt(m, half)
                    invariant
                        m.wf(),
                        two.wf(),
                        half.wf(),
                        down <= MAX_BINARY_SHIFTS,
                    decreases MAX_BINARY_SHIFTS - down,
                {
                    m = Q::mul(m, two);
                    down = down + 1;
                }
                // z = (m - 1) / (m + 1), in [-1/3, 1/3] for m in [1/2, 2].
                let one = Q::one();
                let z = Q::div(Q::sub(m, one), Q::add(m, one));
                let ln_m = Q::mul(two, atanh_series(z));
                // k is the net number of doublings undone; `up` and `down` are
                // never both nonzero, so this cannot overflow an i64.
                let k = Q::sub(Q::new(up as i64, 1), Q::new(down as i64, 1));
                Q::add(ln_m, Q::mul(k, ln2()))
            },
        }
    }

    /// `self` raised to the power `e`, for a negative exponent as well as a
    /// positive one.
    ///
    /// `pow_i32(a, -n)` is `recip(pow_u32(a, n))`, so it inherits both the
    /// exactness of reciprocation on nonzero rationals and the division
    /// conventions: `pow_i32(0, -1)` is `PosInf`, not a panic.
    pub fn pow_i32(self, e: i32) -> (r: Q)
        requires
            self.wf(),
        ensures
            r.wf(),
    {
        if e >= 0 {
            self.pow_u32(e as u32)
        } else {
            // `-e` for `e == i32::MIN` would overflow, so widen first.
            let n: i64 = -(e as i64);
            self.pow_u32(n as u32).recip()
        }
    }
}

/// Terms of the `atan` series, whose argument is reduced to `|z| <= 1/2`.
///
/// The tail at `k` is `2^-(2k+1)/(2k+1)`. At `k = 28` the tail is `1.2e-19`,
/// which is below the grid. At `k = 27` the tail is `5.1e-19`, which is above
/// the grid. This is the longest series in this module. The coefficients of
/// `atan` are `1/(2k+1)`, thus the series converges geometrically. The `sin`
/// and `exp` series converge factorially.
const ATAN_TERMS: u32 = 30;

/// The largest argument `sin`, `cos` and `tan` will accept.
///
/// Above this limit the result has no meaning, and the functions return `Nan`.
/// Argument reduction needs `x mod (π/2)`. This module knows `π` to a relative
/// error of `2^-61`, thus the reduced argument has an absolute error of
/// approximately `|x| · 2^-61`. At `|x| = 2^20` that error is `2^-41`, and the
/// result is still usable. At `|x| = 2^61` the error is larger than `π`, and
/// each digit of the answer is noise.
///
/// `f64` returns a plausible value in that range. This module returns `Nan`,
/// which is the convention of the crate: an explicit non-answer instead of a
/// silent wrong answer.
const TRIG_ARG_LIMIT: i64 = 1 << 20;

/// `atan(z) = z − z³/3 + z⁵/5 − …`, for `|z| <= 1/2`.
///
/// This series is the alternating form of [`atanh_series`]. Subtraction and
/// addition alternate between terms.
fn atan_series(z: Q) -> (r: Q)
    requires
        z.wf(),
    ensures
        r.wf(),
{
    let z2 = Q::mul(z, z);
    let mut term = z;
    let mut sum = z;
    let mut k: u32 = 1;
    while k < ATAN_TERMS
        invariant
            term.wf(),
            sum.wf(),
            z2.wf(),
            1 <= k <= ATAN_TERMS,
        decreases ATAN_TERMS - k,
    {
        term = Q::mul(term, z2);
        let piece = Q::div(term, Q::new((2 * k + 1) as i64, 1));
        sum = if k % 2 == 1 {
            Q::sub(sum, piece)
        } else {
            Q::add(sum, piece)
        };
        k = k + 1;
    }
    sum
}

/// `π`, by Machin's formula `π = 16·atan(1/5) − 4·atan(1/239)`.
///
/// Machin's formula keeps both arguments well inside the range of the series.
/// The simpler form `π/4 = atan(1)` puts the argument at the point where the
/// series converges slowest.
///
/// This function is the derivation of [`pi`], which returns the same value as a
/// literal. This function evaluates two full series, which is approximately
/// sixty-four terms. That cost dominates `sin`, `cos` and `atan`, which each
/// need `π` on every call.
pub fn pi_series() -> (r: Q)
    ensures
        r.wf(),
{
    let a = Q::mul(Q::new(16, 1), atan_series(Q::new(1, 5)));
    let b = Q::mul(Q::new(4, 1), atan_series(Q::new(1, 239)));
    Q::sub(a, b)
}

/// `π`.
///
/// The literal is the value that [`pi_series`] computes. The test
/// `pi_is_the_series_value` asserts that the two are bit-identical. See [`ln2`]
/// for the reason to use a checked literal.
pub fn pi() -> (r: Q)
    ensures
        r.wf(),
{
    Q::new(1811004864519280709, 576460752303423488)
}

/// `π/2`.
pub fn half_pi() -> (r: Q)
    ensures
        r.wf(),
{
    Q::div(pi(), Q::new(2, 1))
}

/// Nearest integer to a `Q`, ties away from zero; `0` for any special.
///
/// Only used on values already known to be small, so the `i64` arithmetic
/// cannot overflow: `|num| <= MAX_MAG` and `den/2 <= MAX_MAG/2` make the sum at
/// most `1.5 · MAX_MAG`.
fn round_to_int(q: Q) -> (r: i64)
    requires
        q.wf(),
{
    match q {
        Q::Number(x) => {
            let n = x.numerator();
            let d = x.denominator();
            if n >= 0 {
                (n + d / 2) / d
            } else {
                (n - d / 2) / d
            }
        },
        _ => 0,
    }
}

/// `sin(z)` by Maclaurin series, for `|z| <= π/4`.
fn sin_series(z: Q) -> (r: Q)
    requires
        z.wf(),
    ensures
        r.wf(),
{
    let z2 = Q::mul(z, z);
    let mut term = z;
    let mut sum = z;
    let mut k: u32 = 1;
    while k < TRIG_TERMS
        invariant
            term.wf(),
            sum.wf(),
            z2.wf(),
            1 <= k <= TRIG_TERMS,
        decreases TRIG_TERMS - k,
    {
        // term_{k} = term_{k-1} · z² / ((2k)(2k+1))
        let kk: i64 = k as i64;
        assert(1 <= kk <= TRIG_TERMS as i64);
        // `kk <= 20`, so the product is at most `40 * 41`. The prover needs
        // this spelled out: a product of two bounded terms is nonlinear.
        assert(2 * kk * (2 * kk + 1) <= 40 * 41) by (nonlinear_arith)
            requires
                1 <= kk <= 11,
        ;
        let d = Q::new(2 * kk * (2 * kk + 1), 1);
        term = Q::div(Q::mul(term, z2), d);
        sum = if k % 2 == 1 {
            Q::sub(sum, term)
        } else {
            Q::add(sum, term)
        };
        k = k + 1;
    }
    sum
}

/// `cos(z)` by Maclaurin series, for `|z| <= π/4`.
fn cos_series(z: Q) -> (r: Q)
    requires
        z.wf(),
    ensures
        r.wf(),
{
    let z2 = Q::mul(z, z);
    let mut term = Q::one();
    let mut sum = Q::one();
    let mut k: u32 = 1;
    while k < TRIG_TERMS
        invariant
            term.wf(),
            sum.wf(),
            z2.wf(),
            1 <= k <= TRIG_TERMS,
        decreases TRIG_TERMS - k,
    {
        // term_{k} = term_{k-1} · z² / ((2k-1)(2k))
        let kk: i64 = k as i64;
        assert(1 <= kk <= TRIG_TERMS as i64);
        assert((2 * kk - 1) * (2 * kk) <= 39 * 40) by (nonlinear_arith)
            requires
                1 <= kk <= 11,
        ;
        let d = Q::new((2 * kk - 1) * (2 * kk), 1);
        term = Q::div(Q::mul(term, z2), d);
        sum = if k % 2 == 1 {
            Q::sub(sum, term)
        } else {
            Q::add(sum, term)
        };
        k = k + 1;
    }
    sum
}

impl Q {
    /// The arctangent, in `(-π/2, π/2)`.
    ///
    /// `atan(±∞)` is exactly `±π/2`. The limit exists and is representable,
    /// thus the infinite cases carry information. `atan(PosSat)` is `Nan`. The
    /// image of `(MAX_MAG, ∞)` is a narrow interval below `π/2` that contains
    /// representable values, thus no saturation state is sound.
    ///
    /// # Method
    ///
    /// Two reductions before the series. `|x| > 1` becomes
    /// `sign(x)·π/2 − atan(1/x)`, and `|x| > 1/2` becomes
    /// `±π/4 + atan((x∓1)/(x±1))`. Together they bring the argument to at most
    /// `1/2`, where thirty-two terms are enough.
    pub fn atan(self) -> (r: Q)
        requires
            self.wf(),
        ensures
            r.wf(),
            self.spec_is_nan() ==> r.spec_is_nan(),
    {
        match self {
            Q::Nan => Q::Nan,
            Q::PosSat => Q::Nan,
            Q::NegSat => Q::Nan,
            Q::PosInf => half_pi(),
            Q::NegInf => half_pi().neg(),
            Q::Number(x) => {
                let q = Q::Number(x);
                let one = Q::one();
                let half = Q::new(1, 2);
                // One `pi()` for both uses below; the reduction needs a quarter
                // and the reciprocal branch needs a half.
                let p = pi();
                let quarter_pi = Q::div(p, Q::new(4, 1));
                let big = Q::gt(q.abs(), one);
                // Reduce |x| > 1 by reciprocation.
                let base = if big {
                    Q::div(one, q)
                } else {
                    q
                };
                // Reduce |base| > 1/2 by the tangent addition formula.
                let (core, shift) = if Q::gt(base, half) {
                    (Q::div(Q::sub(base, one), Q::add(base, one)), quarter_pi)
                } else if Q::lt(base, half.neg()) {
                    (Q::div(Q::add(base, one), Q::sub(one, base)), quarter_pi.neg())
                } else {
                    (base, Q::zero())
                };
                let inner = Q::add(atan_series(core), shift);
                if big {
                    // atan(x) = sign(x)·π/2 − atan(1/x)
                    let hp = Q::div(p, Q::new(2, 1));
                    if Q::gt(q, Q::zero()) {
                        Q::sub(hp, inner)
                    } else {
                        Q::sub(hp.neg(), inner)
                    }
                } else {
                    inner
                }
            },
        }
    }

    /// The sine.
    ///
    /// The result is `Nan` for `|self| > 2^20` and for each special value. The
    /// reduction limit is `2^20`. Both infinities give `Nan`, because `sin` has
    /// no limit at infinity.
    ///
    /// # Method
    ///
    /// `n = round(x / (π/2))`, `r = x − n·(π/2)` with `|r| <= π/4`, then the
    /// Maclaurin series for `sin` or `cos` selected by `n mod 4`.
    pub fn sin(self) -> (r: Q)
        requires
            self.wf(),
        ensures
            r.wf(),
    {
        Q::sin_cos(self, false)
    }

    /// The cosine. Same domain and method as [`Q::sin`].
    pub fn cos(self) -> (r: Q)
        requires
            self.wf(),
        ensures
            r.wf(),
    {
        Q::sin_cos(self, true)
    }

    /// The shared reduction for [`Q::sin`] and [`Q::cos`].
    ///
    /// `want_cos` selects the function to return. Both functions need the same
    /// argument reduction. One shared reduction keeps them consistent, which
    /// the identity `sin(x)² + cos(x)² == 1` needs.
    fn sin_cos(self, want_cos: bool) -> (r: Q)
        requires
            self.wf(),
        ensures
            r.wf(),
    {
        match self {
            Q::Number(x) => {
                let q = Q::Number(x);
                let limit = Q::new(TRIG_ARG_LIMIT, 1);
                if Q::gt(q.abs(), limit) {
                    return Q::Nan;
                }
                let hp = half_pi();
                let n = round_to_int(Q::div(q, hp));
                let r = Q::sub(q, Q::mul(Q::new(n, 1), hp));
                // `n mod 4`, normalised into 0..3 for negative `n` too.
                let m = ((n % 4) + 4) % 4;
                let idx = if want_cos {
                    (m + 1) % 4
                } else {
                    m
                };
                // sin(r + k·π/2) cycles sin, cos, −sin, −cos; cos is the same
                // cycle one quarter-turn ahead, which is what `idx` encodes.
                if idx == 0 {
                    sin_series(r)
                } else if idx == 1 {
                    cos_series(r)
                } else if idx == 2 {
                    sin_series(r).neg()
                } else {
                    cos_series(r).neg()
                }
            },
            // sin and cos have no limit at infinity, and no saturation state
            // can bound a value that oscillates in [-1, 1].
            _ => Q::Nan,
        }
    }

    /// The tangent, as `sin/cos`.
    ///
    /// At an odd multiple of `π/2` the cosine is near zero. The quotient then
    /// saturates or gives an infinity, and does not trap. `tan` has a pole at
    /// those points.
    pub fn tan(self) -> (r: Q)
        requires
            self.wf(),
        ensures
            r.wf(),
    {
        Q::div(self.sin(), self.cos())
    }
}


/// `ln(10)`, by applying [`Q::ln`] to ten.
///
/// The derivation of [`ln10`]; see [`ln2`] for why the value is pinned.
pub fn ln10_series() -> (r: Q)
    ensures
        r.wf(),
{
    Q::new(10, 1).ln()
}

/// `ln(10)`.
///
/// The value is a literal, as for [`ln2`], and `ln10_is_the_series_value`
/// checks it against the derivation. The test is necessary: a literal that
/// comes from a decimal expansion can be wrong in an early significant
/// figure.
pub fn ln10() -> (r: Q)
    ensures
        r.wf(),
{
    Q::new(2654699869899991811, 1152921504606846976)
}

impl Q {
    /// The base-2 logarithm, as `ln(self) / ln(2)`.
    pub fn log2(self) -> (r: Q)
        requires
            self.wf(),
        ensures
            r.wf(),
    {
        Q::div(self.ln(), ln2())
    }

    /// The base-10 logarithm, as `ln(self) / ln(10)`.
    pub fn log10(self) -> (r: Q)
        requires
            self.wf(),
        ensures
            r.wf(),
    {
        Q::div(self.ln(), ln10())
    }

    /// The logarithm in an arbitrary base, as `ln(self) / ln(base)`.
    ///
    /// A base of `1` gives a zero denominator, thus an infinity or `Nan`. The
    /// function `log_1` is undefined.
    pub fn log(self, base: Q) -> (r: Q)
        requires
            self.wf(),
            base.wf(),
        ensures
            r.wf(),
    {
        Q::div(self.ln(), base.ln())
    }

    /// `2^self`, as `exp(self · ln 2)`.
    pub fn exp2(self) -> (r: Q)
        requires
            self.wf(),
        ensures
            r.wf(),
    {
        Q::mul(self, ln2()).exp()
    }

    /// `self^exponent` for a real exponent, as `exp(exponent · ln(self))`.
    ///
    /// The function is defined only for a positive base. `ln` of a negative
    /// value is `Nan`, and that state propagates. `(-8)^(1/3)` has a real
    /// answer and `(-8)^(1/2)` does not, and this function does not separate
    /// the two cases. Use [`Q::pow_i32`] for integer exponents. That function
    /// is exact and accepts negative bases.
    ///
    /// `0^0` is `1`, matching [`Q::pow_u32`] and IEEE.
    pub fn powf(self, exponent: Q) -> (r: Q)
        requires
            self.wf(),
            exponent.wf(),
        ensures
            r.wf(),
    {
        if exponent.is_zero() {
            return Q::one();
        }
        if self.is_zero() {
            return Q::zero();
        }
        Q::mul(exponent, self.ln()).exp()
    }

    /// The cube root, defined for negative arguments as well as positive.
    ///
    /// `cbrt(-x) == -cbrt(x)`, thus the domain is the whole real line, unlike
    /// the domain of [`Q::sqrt`]. The function computes `exp(ln|x| / 3)` and
    /// then applies the sign. Its accuracy is thus the accuracy of `exp` and
    /// `ln`, which is approximately `2^-53`. The accuracy of `sqrt` is
    /// approximately `2^-60`.
    pub fn cbrt(self) -> (r: Q)
        requires
            self.wf(),
        ensures
            r.wf(),
            self.spec_is_nan() ==> r.spec_is_nan(),
    {
        match self {
            Q::Nan => Q::Nan,
            Q::PosInf => Q::PosInf,
            Q::NegInf => Q::NegInf,
            // Same argument as `sqrt(PosSat)`: the image of `(MAX_MAG, inf)`
            // under a root reaches far below `MAX_MAG`.
            Q::PosSat => Q::Nan,
            Q::NegSat => Q::Nan,
            Q::Number(x) => {
                let s = x.signum();
                if s == 0 {
                    return Q::zero();
                }
                let mag = Q::Number(x).abs();
                let root = Q::div(mag.ln(), Q::new(3, 1)).exp();
                if s < 0 {
                    root.neg()
                } else {
                    root
                }
            },
        }
    }

    /// `sqrt(self² + other²)`, without the intermediate overflowing where the
    /// naive form would.
    ///
    /// The function computes `|a|·sqrt(1 + (b/a)²)`, where `a` is the operand
    /// with the larger magnitude. The squared term is thus at most `1` and
    /// stays representable when `a² + b²` does not.
    pub fn hypot(self, other: Q) -> (r: Q)
        requires
            self.wf(),
            other.wf(),
        ensures
            r.wf(),
    {
        let a = self.abs();
        let b = other.abs();
        let (big, small) = if Q::ge(a, b) {
            (a, b)
        } else {
            (b, a)
        };
        if big.is_zero() {
            return Q::zero();
        }
        let ratio = Q::div(small, big);
        Q::mul(big, Q::add(Q::one(), Q::mul(ratio, ratio)).sqrt())
    }

    /// The hyperbolic sine, `(e^x - e^-x) / 2`.
    pub fn sinh(self) -> (r: Q)
        requires
            self.wf(),
        ensures
            r.wf(),
    {
        Q::div(Q::sub(self.exp(), self.neg().exp()), Q::new(2, 1))
    }

    /// The hyperbolic cosine, `(e^x + e^-x) / 2`.
    pub fn cosh(self) -> (r: Q)
        requires
            self.wf(),
        ensures
            r.wf(),
    {
        Q::div(Q::add(self.exp(), self.neg().exp()), Q::new(2, 1))
    }

    /// The hyperbolic tangent, `sinh / cosh`.
    ///
    /// `cosh` is never zero, thus this function has no poles, unlike
    /// [`Q::tan`]. Large arguments give results near `±1`.
    pub fn tanh(self) -> (r: Q)
        requires
            self.wf(),
        ensures
            r.wf(),
    {
        Q::div(self.sinh(), self.cosh())
    }

    /// The arcsine, in `[-π/2, π/2]`.
    ///
    /// The result is `Nan` outside `[-1, 1]`, where there is no real answer.
    /// The function computes the endpoints directly. The identity below divides
    /// by zero at those two points.
    pub fn asin(self) -> (r: Q)
        requires
            self.wf(),
        ensures
            r.wf(),
    {
        match self {
            Q::Number(x) => {
                let q = Q::Number(x);
                let one = Q::one();
                if Q::gt(q.abs(), one) {
                    return Q::Nan;
                }
                if q.abs() == one {
                    let hp = Q::div(pi(), Q::new(2, 1));
                    return if Q::gt(q, Q::zero()) {
                        hp
                    } else {
                        hp.neg()
                    };
                }
                // asin(x) = atan(x / sqrt(1 - x²))
                let denom = Q::sub(one, Q::mul(q, q)).sqrt();
                Q::div(q, denom).atan()
            },
            // Every special lies outside [-1, 1] or carries no information.
            _ => Q::Nan,
        }
    }

    /// The arccosine, in `[0, π]`, as `π/2 - asin(self)`.
    pub fn acos(self) -> (r: Q)
        requires
            self.wf(),
        ensures
            r.wf(),
    {
        Q::sub(Q::div(pi(), Q::new(2, 1)), self.asin())
    }

    /// The two-argument arctangent: the angle of `(x, y)` from the positive
    /// x-axis, in `(-π, π]`.
    ///
    /// The quadrant corrections distinguish this function from `atan(y/x)`,
    /// which gives the same result for `(-1, -1)` and `(1, 1)`. `atan2(0, 0)`
    /// is `Nan`, because the origin has no angle.
    pub fn atan2(self, x: Q) -> (r: Q)
        requires
            self.wf(),
            x.wf(),
        ensures
            r.wf(),
    {
        let y = self;
        let zero = Q::zero();
        let p = pi();
        let hp = Q::div(p, Q::new(2, 1));
        if y.is_nan() || x.is_nan() {
            return Q::Nan;
        }
        if x.is_zero() && y.is_zero() {
            return Q::Nan;
        }
        if x.is_zero() {
            return if Q::gt(y, zero) {
                hp
            } else {
                hp.neg()
            };
        }
        let base = Q::div(y, x).atan();
        if Q::gt(x, zero) {
            base
        } else if Q::ge(y, zero) {
            Q::add(base, p)
        } else {
            Q::sub(base, p)
        }
    }
}

} // verus!
