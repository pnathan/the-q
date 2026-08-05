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
    /// Newton's iteration `y <- (y + x/y)/2` converges quadratically and from
    /// above once past the first step, so a fixed eight iterations from the
    /// integer-root seed is comfortably past the point where further steps
    /// cannot change the rounded answer.
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
                    while i < 8
                        invariant
                            y.wf(),
                            q.wf(),
                            two.wf(),
                            i <= 8,
                        decreases 8 - i,
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

/// Terms of every Maclaurin series here.
///
/// Each series is range-reduced so its argument satisfies `|z| <= 1/2` before
/// summing, and at that argument twenty terms put the tail far below the grid:
/// `(1/2)^20 / 20!` is about `4e-25`, against a grid resolution of `2^-61`
/// (about `4e-19`). The count is fixed rather than derived from a convergence
/// test so that termination is structural and the cost of a call is constant.
const SERIES_TERMS: u32 = 20;

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
                while i <= SERIES_TERMS
                    invariant
                        term.wf(),
                        sum.wf(),
                        z.wf(),
                        1 <= i <= SERIES_TERMS + 1,
                    decreases SERIES_TERMS + 1 - i,
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

} // verus!
