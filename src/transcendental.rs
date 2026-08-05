//! Transcendental and root functions on the extended [`Q`].
//!
//! # These are not rational-closed, and that is the whole difficulty
//!
//! `sqrt(2)`, `exp(1)` and `sin(1)` are irrational, so no rational type can
//! return them. What this module returns is the nearest representable rational
//! to the true value, with a stated error bound — the same bargain the rest of
//! the crate makes for arithmetic, extended to functions that have no exact
//! answer at all.
//!
//! # Termination is structural, not conditional
//!
//! Every iteration here runs a **fixed** number of steps rather than looping
//! until a convergence test passes. That is deliberate on two counts: a fixed
//! count is trivially terminating, which is what lets Verus discharge these at
//! all; and it makes the cost of every call identical and predictable, which a
//! convergence test does not. The counts are chosen so that the iteration has
//! provably converged to within the representable grid before it stops.
//!
//! # Where the error comes from
//!
//! Two independent sources, and they are worth separating:
//!
//! * **Truncation** — the series or iteration is cut off. Bounded by choosing
//!   enough terms that the tail is below the grid resolution.
//! * **Rounding** — every intermediate `Q` operation rounds, contributing at
//!   most `2^-61 · max(1, |value|)` each, accumulating additively over `k`
//!   operations exactly as `nary`'s V8 bound describes.
//!
//! The second dominates, and it is why these functions are accurate to roughly
//! `2^-55` rather than to the full `2^-61` of a single operation. That is still
//! better than `f64`'s `2^-53`.
//!
//! # Precision degrades for results far below 1, and that is structural
//!
//! Read this before trusting a small result. R3's error bound is
//! `2^-61 · max(1, |exact|)`, which is **absolute** below 1 rather than
//! relative. A value near `1` therefore carries about 61 significant bits, but
//! a value near `2^-43` carries only about 18: the grid spacing is the same, so
//! there are far fewer grid points *relative to the value*.
//!
//! The consequence bites hardest where a function's output is tiny. `exp(-30)`
//! is about `2^-43`, so it is accurate to roughly `2^-18` relatively, and
//! `ln(exp(-30))` comes back off by about `5e-6` — measured at `2^-20` in
//! `ln_inverts_exp_to_the_precision_the_grid_allows`. Neither function is at
//! fault; the intermediate simply could not carry the information.
//!
//! This is the same trade the rest of the crate makes, surfaced where it is
//! most visible. If small values matter, scale the problem so they are not
//! small — the budget is far more generous near `1` than near `0`.
//!
//! # Failure is a value, never a panic
//!
//! Every function here is total. `sqrt` of a negative number is `Nan`, not a
//! panic; `ln(0)` is `NegInf`; arguments whose result cannot be represented
//! saturate. The special-value results are derived from the §2 denotations in
//! issue #26 the same way the arithmetic tables are — a result is sound only if
//! its denotation contains the true image of the operand's denotation.
//!
//! One consequence is worth stating because it surprises people: **`sqrt` of a
//! saturated value is `Nan`**, not `PosSat`. `PosSat` denotes `(MAX_MAG, ∞)`,
//! whose image under `sqrt` is `(2^31, ∞)` — which reaches far below `MAX_MAG`
//! and therefore includes representable values. Answering `PosSat` there would
//! claim a magnitude the value need not have. The same reasoning makes
//! `ln(PosSat)` and `atan(PosSat)` `Nan`.

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
/// Newton's method on integers. Each step strictly decreases the estimate until
/// it settles, which is what `decreases` keys on; the classic formulation would
/// loop `while y < x`, and the guard is exactly the "still decreasing" test.
///
/// `n < 0` yields `0` rather than panicking — callers here never pass one, and
/// a total function is easier to reason about than a guarded one.
/// The postcondition is the *defining* property of an integer square root, not
/// a bound on it: `r*r <= n < (r+1)*(r+1)` pins `r` uniquely.
///
/// That matters here for a concrete reason. An earlier version of this function
/// used the seed `n/2 + 1` instead of `(n+1)/2` and returned `2` for
/// `isqrt(2)`. It carried the weak postcondition `r >= 0 && r <= n`, which that
/// wrong answer satisfies, so **verification passed** and only a test caught it.
/// A specification that admits the bug is not a specification.
///
/// The implementation is Newton for speed followed by a bounded correction.
/// Newton alone lands on the answer, but proving *that* needs AM-GM reasoning
/// over integer division, which is a great deal of proof for no extra
/// behaviour. The correction loops establish the postcondition directly from
/// their own exit conditions, run at most once each in practice, and cost two
/// `i128` multiplications.
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
    // The squares live in variables rather than in the loop guards. Two
    // reasons, both necessary: `r*r` fitting `i128` is a nonlinear fact the
    // prover needs a proof block to reach, and a `while` guard's *negation* is
    // what carries the postcondition out of the loop — a `loop`/`break` form
    // discards exactly that.
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
    /// Newton's iteration `y <- (y + x/y)/2` converges quadratically, so a fixed
    /// seven steps from the integer-root seed is past the point where
    /// further steps cannot change the rounded answer.
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
                        // y <- (y + x/y) / 2. If `y` ever became zero or a
                        // special the division would report it rather than
                        // trapping, and the result would stay a value.
                        y = Q::div(Q::add(y, Q::div(q, y)), two);
                        i = i + 1;
                    }
                    y
                }
            },
            // The image of (MAX_MAG, inf) under sqrt is (2^31, inf), which
            // reaches far below MAX_MAG — so no saturation state is sound.
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
// Each count is derived from its own tail bound against the grid resolution
// `2^-61` (about `4.34e-19`), not shared. A uniform count would be wrong in
// both directions at once: too short for `atan`, whose coefficients are
// `1/(2k+1)`, and nearly twice as long as `sin` needs, whose coefficients are
// `1/(2k+1)!`. Benchmarking made the second cost visible.
//
// Every count is fixed rather than derived from a convergence test, so that
// termination is structural and the cost of a call is constant.
// ---------------------------------------------------------------------------

/// Terms of the `atanh` series, whose argument is reduced to `|z| <= 1/3`.
///
/// The tail at `k` is `3^-(2k+1)/(2k+1)`; `k = 18` gives `6.0e-20`, under the
/// grid, while `k = 17` gives `5.7e-19`, over it. The loop covers `k` up to
/// `SERIES_TERMS - 1 = 19`, one past what is needed.
const SERIES_TERMS: u32 = 20;

/// Terms of the `exp` series, whose argument is reduced to `|z| <= 1/2`.
///
/// The tail at `n` is `2^-n/n!`; `n = 17` gives `2.1e-20`, under the grid,
/// while `n = 16` gives `7.3e-19`, over it. Eighteen covers seventeen with one
/// to spare.
const EXP_TERMS: u32 = 18;

/// Terms of the `sin` and `cos` series, whose argument is reduced to
/// `|z| <= π/4`.
///
/// The tail at `k` is `(π/4)^(2k+1)/(2k+1)!`; `k = 9` gives `8.4e-20`, under
/// the grid, while `k = 8` gives `4.6e-17`, well over it. The loop covers `k`
/// up to `TRIG_TERMS - 1 = 10`.
///
/// This is the count that most rewards being derived rather than shared: the
/// factorial denominators make it converge far faster than `atan`, so reusing
/// `atan`'s length here would have doubled the cost of every `sin` and `cos`
/// for no accuracy at all.
const TRIG_TERMS: u32 = 11;

/// Newton iterations in [`Q::sqrt`].
///
/// The integer-root seed is within a factor of two, so the initial relative
/// error is at most about `1/2`. Newton squares it each step:
/// `0.5 → 0.125 → 7.8e-3 → 3.1e-5 → 4.6e-10 → 1.1e-19`, which is past the grid
/// by the sixth. Seven leaves a margin; eight was simply wasted work.
const SQRT_ITERS: u32 = 7;

/// Maximum halvings used to bring an argument into the series' comfort zone.
///
/// `exp` is only evaluated for `|x| <= 44` (beyond that the result leaves the
/// budget), and `44 / 2^7 < 0.35`, so seven always suffices; eight is carried
/// for margin. The bound also makes the reduction loop trivially terminating.
const MAX_HALVINGS: u32 = 8;

/// Beyond `|x| > 44`, `exp(x)` leaves the budget in one direction or the other:
/// `exp(44) > 2^63` and `exp(-44) < 2^-63`. Both are decided without summing
/// anything.
const EXP_ARG_LIMIT: i64 = 44;

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
    /// `exp(NegSat)` is `Nan` rather than zero, and the asymmetry with
    /// `exp(Number(-50))` is deliberate. The image of `(-∞, -MAX_MAG)` is
    /// `(0, exp(-MAX_MAG))`, an interval that does **not** contain zero, so
    /// `Number(0)` would be unsound as a denotation — it would assert an exact
    /// value the true result provably is not. For a `Number` argument the
    /// rounding contract applies instead and underflow-to-zero is inside it
    /// (#26 §11), which is why that case may answer zero and this one may not.
    /// It is also the same call §11 makes for `recip(Sat)`: a computation
    /// continuing past an overflow is one option (A) declines to serve.
    ///
    /// # Method
    ///
    /// `exp(x) = exp(x / 2^k)^(2^k)`, with `k` chosen as the smallest value
    /// bringing `|x|` to at most `1/2`, then twenty Maclaurin terms, then `k`
    /// squarings. `k` is adaptive rather than fixed because each squaring
    /// doubles the relative error: a fixed `k = 8` would cost every small
    /// argument a factor of 256 in accuracy it does not need.
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
                let limit = Q::new(EXP_ARG_LIMIT, 1);
                let q = Q::Number(x);
                if Q::gt(q, limit) {
                    return Q::PosSat;
                }
                if Q::lt(q, limit.neg()) {
                    return Q::zero();
                }
                let half = Q::new(1, 2);
                let two = Q::new(2, 1);
                // Range reduction: halve until |z| <= 1/2.
                let mut z = q;
                let mut k: u32 = 0;
                while k < MAX_HALVINGS && Q::gt(z.abs(), half)
                    invariant
                        z.wf(),
                        half.wf(),
                        two.wf(),
                        k <= MAX_HALVINGS,
                    decreases MAX_HALVINGS - k,
                {
                    z = Q::div(z, two);
                    k = k + 1;
                }
                // Maclaurin: term_{n+1} = term_n · z / (n+1).
                let mut term = Q::one();
                let mut sum = Q::one();
                let mut i: u32 = 1;
                while i <= EXP_TERMS
                    invariant
                        term.wf(),
                        sum.wf(),
                        z.wf(),
                        1 <= i <= EXP_TERMS + 1,
                    decreases EXP_TERMS + 1 - i,
                {
                    term = Q::div(Q::mul(term, z), Q::new(i as i64, 1));
                    sum = Q::add(sum, term);
                    i = i + 1;
                }
                // Undo the reduction.
                let mut j: u32 = 0;
                while j < k
                    invariant
                        sum.wf(),
                        j <= k,
                        k <= MAX_HALVINGS,
                    decreases k - j,
                {
                    sum = Q::mul(sum, sum);
                    j = j + 1;
                }
                sum
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
/// Every caller range-reduces to that interval first. At `|z| = 1/3` the
/// twentieth odd term is `3^-39 / 39`, about `3e-21`, comfortably below the
/// `2^-61` grid — so the truncation error is invisible and the rounding error
/// dominates, which is the same balance every other series here strikes.
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
/// Kept as the *derivation* of [`e`]. Summed directly rather than as `exp(1)`
/// so that the constant and the function that would otherwise produce it are
/// independent — a bug in `exp`'s range reduction cannot hide inside `e`.
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
/// The literal is exactly what [`e_series`] computes — `e_is_the_series_value`
/// asserts they are bit-identical. See [`ln2`] for why a checked literal is
/// preferable to recomputing a series on every call.
pub fn e() -> (r: Q)
    ensures
        r.wf(),
{
    Q::new(3133965575612453543, 1152921504606846976)
}

/// `ln(2)`, by the series `2·atanh(1/3)`.
///
/// Kept as the *derivation* of [`ln2`], which returns the same value as a
/// literal. Benchmarking showed why: recomputing twenty series terms on every
/// call dominated the cost of everything that used it.
pub fn ln2_series() -> (r: Q)
    ensures
        r.wf(),
{
    Q::mul(Q::new(2, 1), atanh_series(Q::new(1, 3)))
}

/// `ln(2)`.
///
/// The literal is exactly what [`ln2_series`] computes — `ln2_is_the_series_value`
/// asserts the two are bit-identical, so the constant is derived and checked
/// rather than asserted. That test is what makes a hard-coded value acceptable
/// here: it can be re-derived by running the suite, and it fails loudly if the
/// series, the width budget or the rounding contract ever changes.
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
    /// Binary range reduction to `m ∈ [1/2, 2]`, then
    /// `ln(m) = 2·atanh((m-1)/(m+1))` — whose argument is then at most `1/3` in
    /// magnitude, which is exactly the interval the series is accurate on —
    /// and finally `ln(x) = ln(m) + k·ln(2)`.
    ///
    /// The `atanh` form is used rather than the direct `ln(1+u)` series because
    /// its terms are all odd powers of a much smaller argument: for `m` at the
    /// end of the reduced range, `u` would be `1` and the direct series would
    /// not converge at all.
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
/// The tail at `k` is `2^-(2k+1)/(2k+1)`; `k = 28` gives `1.2e-19`, under the
/// grid, while `k = 27` gives `5.1e-19`, over it. This is by far the longest
/// series here — `atan`'s coefficients are `1/(2k+1)`, so it converges
/// geometrically where `sin` and `exp` converge factorially.
const ATAN_TERMS: u32 = 30;

/// The largest argument `sin`, `cos` and `tan` will accept.
///
/// Beyond this the answer is not merely inaccurate, it is meaningless, and the
/// functions return `Nan` rather than a number nobody should trust. Argument
/// reduction needs `x mod (π/2)`, and `π` is known here only to a relative
/// `2^-61`, so the reduced argument carries an absolute error of about
/// `|x| · 2^-61`. At `|x| = 2^20` that is `2^-41`, which still leaves the
/// result usable; at `|x| = 2^61` it exceeds `π` itself and every digit of the
/// answer is noise.
///
/// `f64` returns a plausible-looking value in that regime. This returns `Nan`,
/// which is the same choice the rest of the crate makes: an explicit
/// non-answer beats a silent wrong one.
const TRIG_ARG_LIMIT: i64 = 1 << 20;

/// `atan(z) = z − z³/3 + z⁵/5 − …`, for `|z| <= 1/2`.
///
/// The alternating sibling of [`atanh_series`]; subtraction and addition
/// alternate rather than every term adding.
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
/// Machin's form is chosen because both arguments sit deep in the series'
/// comfortable range — the naive `π/4 = atan(1)` would put the argument exactly
/// where the series barely converges.
///
/// Kept as the *derivation* of [`pi`], which returns the same value as a
/// literal. This costs two full series — about sixty-four terms — and
/// benchmarking showed it dominating `sin`, `cos` and `atan`, each of which
/// needed it on every call.
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
/// The literal is exactly what [`pi_series`] computes — `pi_is_the_series_value`
/// asserts they are bit-identical. See [`ln2`] for why a checked literal is
/// preferable to recomputing here.
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
    /// `atan(±∞)` is `±π/2` exactly — the limit exists and is representable, so
    /// unlike most functions here the infinite cases carry real information.
    /// `atan(PosSat)` is `Nan`: the image of `(MAX_MAG, ∞)` is a sliver just
    /// below `π/2`, which contains representable values and so cannot be
    /// reported as any saturation state.
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
    /// `Nan` for `|self| > 2^20`, for every special, and for anything else whose
    /// argument cannot be reduced meaningfully — the limit is `2^20`. Both
    /// infinities are `Nan` because `sin` has no limit at infinity, which is a
    /// genuine non-answer rather than a limitation of this implementation.
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
    /// `want_cos` selects which of the pair is returned; both need the identical
    /// argument reduction, and doing it once keeps them exactly consistent —
    /// `sin(x)² + cos(x)² == 1` would be at the mercy of two separate reductions
    /// otherwise.
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
    /// At an odd multiple of `π/2` the cosine is near zero and the quotient
    /// saturates or reports an infinity rather than trapping — which is the
    /// honest answer, since `tan` genuinely has a pole there.
    pub fn tan(self) -> (r: Q)
        requires
            self.wf(),
        ensures
            r.wf(),
    {
        Q::div(self.sin(), self.cos())
    }
}

} // verus!
