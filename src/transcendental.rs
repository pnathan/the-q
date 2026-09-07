//! Roots and transcendental functions on [`Q`].
//!
//! None of these is rational-closed, so each returns a nearby representable
//! rational. Every series and iteration runs a fixed number of steps chosen so
//! the truncation tail is below the `2^-61` grid; the term counts are derived
//! beside each constant. Termination is therefore structural, and Verus proves
//! totality and well-formedness of every result. Accuracy is measured, not
//! proven: `README.md` has the table, from two independent oracles.
//!
//! The dominant error is rounding of intermediates, and it is absolute below
//! 1 (R3), so relative accuracy falls off for small results. Special values
//! follow the denotations in issue #26: a result is sound only if its
//! denotation contains the true image of the operand's. That is why
//! `sqrt(PosSat)`, `ln(PosSat)` and `atan(PosSat)` are `Nan` — the image of
//! `(MAX_MAG, ∞)` under each reaches back inside the budget.

use verus_builtin_macros::verus;

#[allow(unused_imports)]
use verus_builtin::*;
#[allow(unused_imports)]
use vstd::prelude::*;

use crate::ext::{Q, Sign};
use crate::types::Rat;

verus! {

/// Integer square root, `r*r <= n < (r+1)*(r+1)`; `0` for `n < 0`. Newton on
/// integers, then a bounded correction whose exit conditions establish the
/// postcondition directly (Newton alone would need AM-GM over integer
/// division).
///
/// Public only because Verus's visibility rules require it; not part of the
/// semver-stable API.
///
/// ```
/// assert_eq!(the_q::transcendental::isqrt_i64(10), 3);
/// assert_eq!(the_q::transcendental::isqrt_i64(16), 4);
/// ```
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

/// The `isqrt` contract admits exactly one value.
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

/// `isqrt` is monotone, stated on the contract.
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

/// On a perfect square `k·k` the contract forces `k`.
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
    /// The square root. Negative → `Nan`; `PosSat` → `Nan` (its image reaches
    /// below `MAX_MAG`); `PosInf` → `PosInf`. Seven Newton steps from the
    /// integer-root seed.
    ///
    /// ```
    /// use the_q::Q;
    ///
    /// assert_eq!(Q::new(4, 1).sqrt(), Q::new(2, 1));
    /// assert_eq!(Q::PosSat.sqrt(), Q::Nan);
    /// ```
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


/// Terms of the `sin`/`cos` series on `|z| <= π/4`: the tail at `k = 9` is
/// `8.4e-20`, under the grid; at `k = 8`, `4.6e-17`.
const TRIG_TERMS: u32 = 11;

/// Newton iterations in [`Q::sqrt`]: the seed is within a factor of two and
/// the error squares each step, so six reach the grid; seven is margin.
const SQRT_ITERS: u32 = 7;


/// Beyond `|x| > 44`, `exp(x)` leaves the budget in one direction or the other:
/// `exp(44) > 2^63` and `exp(-44) < 2^-63`. Both are decided without summing
/// anything.
const EXP_ARG_LIMIT: i64 = 44;

/// Beyond `|x| > 22`, `e^-|x| < 2^-62 · e^|x|`, so the hyperbolic functions
/// are a single exponential to within the rounding contract.
const HYP_ARG_LIMIT: i64 = 22;

/// Canonical bounded-rational approximation of π used throughout this module.
pub const PI_NUM: i64 = 1_811_004_864_519_280_709;
pub const PI_DEN: i64 = 576_460_752_303_423_488;

/// Quotient/remainder decomposition used by [`fx_to_grid`].
pub proof fn lemma_fx_to_grid_decomposition(m: int, d: int, q: int, rem: int)
    requires
        0 <= m,
        0 < d,
        q == (m * crate::fx::FX_ONE as int) / d,
        rem == (m * crate::fx::FX_ONE as int) % d,
    ensures
        m * crate::fx::FX_ONE as int == q * d + rem,
        0 <= rem < d,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(
        m * crate::fx::FX_ONE as int,
        d,
    );
    vstd::arithmetic::div_mod::lemma_mod_bound(m * crate::fx::FX_ONE as int, d);
}

/// The selected grid point is within half a grid cell of the exact scaled
/// value.
pub proof fn lemma_fx_to_grid_nearest(
    m: int,
    d: int,
    q: int,
    rem: int,
    rounded: int,
)
    requires
        0 <= m,
        0 < d,
        m * crate::fx::FX_ONE as int == q * d + rem,
        0 <= rem < d,
        rounded == if 2 * rem > d || (2 * rem == d && q % 2 == 1) {
            q + 1
        } else {
            q
        },
    ensures
        2 * crate::model::abs_int(rounded * d - m * crate::fx::FX_ONE as int) <= d,
{
    let scaled = m * crate::fx::FX_ONE as int;
    assert(scaled == q * d + rem);
    if 2 * rem > d || (2 * rem == d && q % 2 == 1) {
        assert(rounded == q + 1);
        assert(2 * rem >= d);
        assert(rounded * d == (q + 1) * d) by (nonlinear_arith)
            requires
                rounded == q + 1,
        ;
        assert((q + 1) * d == q * d + d) by (nonlinear_arith);
        assert(rounded * d - scaled == d - rem);
        assert(0 <= d - rem);
        assert(crate::model::abs_int(d - rem) == d - rem);
        assert(2 * (d - rem) <= d);
    } else {
        assert(rounded == q);
        assert(2 * rem <= d);
        assert(rounded * d == q * d);
        assert(rounded * d - scaled == -rem);
        assert(crate::model::abs_int(-rem) == rem);
    }
}

/// An exact half-cell case selects an even grid integer.
pub proof fn lemma_fx_to_grid_ties_even(
    m: int,
    d: int,
    q: int,
    rem: int,
    rounded: int,
)
    requires
        0 <= m,
        0 < d,
        m * crate::fx::FX_ONE as int == q * d + rem,
        0 <= rem < d,
        rounded == if 2 * rem > d || (2 * rem == d && q % 2 == 1) {
            q + 1
        } else {
            q
        },
    ensures
        2 * crate::model::abs_int(rounded * d - m * crate::fx::FX_ONE as int) == d
            ==> rounded % 2 == 0,
{
    let scaled = m * crate::fx::FX_ONE as int;
    assert(scaled == q * d + rem);
    vstd::arithmetic::div_mod::lemma_mod_bound(q, 2);
    if 2 * rem > d || (2 * rem == d && q % 2 == 1) {
        assert(rounded == q + 1);
        assert(2 * rem >= d);
        assert(rounded * d == (q + 1) * d) by (nonlinear_arith)
            requires
                rounded == q + 1,
        ;
        assert((q + 1) * d == q * d + d) by (nonlinear_arith);
        assert(rounded * d - scaled == d - rem);
        assert(crate::model::abs_int(d - rem) == d - rem);
        if 2 * crate::model::abs_int(rounded * d - m * crate::fx::FX_ONE as int) == d {
            assert(2 * rem == d);
            assert(q % 2 == 1);
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(q, 2);
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
                q + 1,
                2,
                q / 2 + 1,
                0,
            );
        }
    } else {
        assert(rounded == q);
        assert(2 * rem <= d);
        assert(rounded * d == q * d);
        assert(rounded * d - scaled == -rem);
        assert(crate::model::abs_int(-rem) == rem);
        if 2 * crate::model::abs_int(rounded * d - m * crate::fx::FX_ONE as int) == d {
            assert(2 * rem == d);
            assert(q % 2 != 1);
            assert(q % 2 == 0);
        }
    }
}

/// Rounding the supported input range cannot exceed the fixed-point engine's
/// input budget.
pub proof fn lemma_fx_to_grid_bound(
    m: int,
    d: int,
    q: int,
    rem: int,
    rounded: int,
    neg: bool,
)
    requires
        0 <= m,
        0 < d,
        m * crate::fx::FX_ONE as int == q * d + rem,
        0 <= rem < d,
        rounded == if 2 * rem > d || (2 * rem == d && q % 2 == 1) {
            q + 1
        } else {
            q
        },
        m * crate::fx::FX_ONE as int <= 405828369621610135552int * d,
    ensures
        crate::model::abs_int(if neg { -rounded } else { rounded })
            <= 406000000000000000000int,
{
    let scaled = m * crate::fx::FX_ONE as int;
    vstd::arithmetic::mul::lemma_mul_nonnegative(m, crate::fx::FX_ONE as int);
    assert(scaled >= 0);
    assert(scaled == q * d + rem);
    if q < 0 {
        assert(q <= -1);
        assert(q * d <= -d) by (nonlinear_arith)
            requires
                q <= -1,
                d > 0,
        ;
        assert(scaled < 0);
        assert(false);
    }
    assert(q * d <= scaled);
    assert(q * d <= 405828369621610135552int * d);
    if q > 405828369621610135552int {
        assert(q >= 405828369621610135553int);
        assert(q * d >= 405828369621610135553int * d) by (nonlinear_arith)
            requires
                q >= 405828369621610135553int,
                d > 0,
        ;
        assert(q * d > 405828369621610135552int * d) by (nonlinear_arith)
            requires
                d > 0,
                q * d >= 405828369621610135553int * d,
        ;
        assert(false);
    }
    assert(q <= rounded <= q + 1);
    assert(rounded <= 405828369621610135553int);
    assert(405828369621610135553int <= 406000000000000000000int) by (compute);
    if neg {
        assert(crate::model::abs_int(-rounded) == rounded);
    } else {
        assert(crate::model::abs_int(rounded) == rounded);
    }
}

/// Exact rounded target for the four cases where both `atan2` coordinates are
/// infinite. Other inputs map to zero so the model remains total.
pub open spec fn atan2_inf_target(y: Q, x: Q) -> Rat {
    match (y, x) {
        (Q::PosInf, Q::PosInf) => crate::round::round_frac(
            PI_NUM as int,
            4 * PI_DEN as int,
            crate::types::Dir::Nearest,
        ),
        (Q::PosInf, Q::NegInf) => crate::round::round_frac(
            3 * PI_NUM as int,
            4 * PI_DEN as int,
            crate::types::Dir::Nearest,
        ),
        (Q::NegInf, Q::PosInf) => crate::round::round_frac(
            -(PI_NUM as int),
            4 * PI_DEN as int,
            crate::types::Dir::Nearest,
        ),
        (Q::NegInf, Q::NegInf) => crate::round::round_frac(
            -(3 * PI_NUM as int),
            4 * PI_DEN as int,
            crate::types::Dir::Nearest,
        ),
        _ => crate::round::round_frac(0, 1, crate::types::Dir::Nearest),
    }
}

/// Executable counterpart of [`atan2_inf_target`].
fn atan2_inf_target_exec(y: Q, x: Q) -> (r: Rat)
    requires
        y.wf(),
        x.wf(),
    ensures
        r == atan2_inf_target(y, x),
        r.wf(),
{
    proof {
        crate::model::lemma_pow2_126();
        crate::model::lemma_pow2_124();
    }
    match (y, x) {
        (Q::PosInf, Q::PosInf) => {
            crate::round::round_frac_exec(
                PI_NUM as i128,
                4 * PI_DEN as i128,
                crate::types::Dir::Nearest,
            )
        },
        (Q::PosInf, Q::NegInf) => {
            crate::round::round_frac_exec(
                3 * PI_NUM as i128,
                4 * PI_DEN as i128,
                crate::types::Dir::Nearest,
            )
        },
        (Q::NegInf, Q::PosInf) => {
            crate::round::round_frac_exec(
                -(PI_NUM as i128),
                4 * PI_DEN as i128,
                crate::types::Dir::Nearest,
            )
        },
        (Q::NegInf, Q::NegInf) => {
            crate::round::round_frac_exec(
                -(3 * PI_NUM as i128),
                4 * PI_DEN as i128,
                crate::types::Dir::Nearest,
            )
        },
        _ => crate::round::round_frac_exec(0, 1, crate::types::Dir::Nearest),
    }
}

/// Every infinity-pair target satisfies the bounded-rational invariant.
pub proof fn lemma_atan2_inf_target_wf(y: Q, x: Q)
    ensures
        atan2_inf_target(y, x).wf(),
{
    match (y, x) {
        (Q::PosInf, Q::PosInf) => {
            crate::round::lemma_round_frac_wf(
                PI_NUM as int,
                4 * PI_DEN as int,
                crate::types::Dir::Nearest,
            );
        },
        (Q::PosInf, Q::NegInf) => {
            crate::round::lemma_round_frac_wf(
                3 * PI_NUM as int,
                4 * PI_DEN as int,
                crate::types::Dir::Nearest,
            );
        },
        (Q::NegInf, Q::PosInf) => {
            crate::round::lemma_round_frac_wf(
                -(PI_NUM as int),
                4 * PI_DEN as int,
                crate::types::Dir::Nearest,
            );
        },
        (Q::NegInf, Q::NegInf) => {
            crate::round::lemma_round_frac_wf(
                -(3 * PI_NUM as int),
                4 * PI_DEN as int,
                crate::types::Dir::Nearest,
            );
        },
        _ => {
            crate::round::lemma_round_frac_wf(0, 1, crate::types::Dir::Nearest);
        },
    }
}

/// The infinite-coordinate \`atan2\` targets have the sign of the vertical coordinate.
pub proof fn lemma_atan2_inf_target_sign(y: Q, x: Q)
    requires
        y.spec_is_infinite(),
        x.spec_is_infinite(),
    ensures
        y == Q::PosInf ==> atan2_inf_target(y, x).n() > 0,
        y == Q::NegInf ==> atan2_inf_target(y, x).n() < 0,
{
    match (y, x) {
        (Q::PosInf, Q::PosInf) => {
            Rat::lemma_from_raw_spec_components(1_811_004_864_519_280_709, 2_305_843_009_213_693_952);
            assert(crate::round::round_frac(PI_NUM as int, 4 * PI_DEN as int, crate::types::Dir::Nearest)
                == Rat::from_raw_spec(1_811_004_864_519_280_709, 2_305_843_009_213_693_952)) by (compute);
            assert(crate::round::round_frac(PI_NUM as int, 4 * PI_DEN as int, crate::types::Dir::Nearest).n() > 0) by (compute);
        },
        (Q::PosInf, Q::NegInf) => {
            Rat::lemma_from_raw_spec_components(339_563_412_097_365_133, 144_115_188_075_855_872);
            assert(crate::round::round_frac(3 * PI_NUM as int, 4 * PI_DEN as int, crate::types::Dir::Nearest)
                == Rat::from_raw_spec(339_563_412_097_365_133, 144_115_188_075_855_872)) by (compute);
            assert(crate::round::round_frac(3 * PI_NUM as int, 4 * PI_DEN as int, crate::types::Dir::Nearest).n() > 0) by (compute);
        },
        (Q::NegInf, Q::PosInf) => {
            Rat::lemma_from_raw_spec_components(-1_811_004_864_519_280_709i64, 2_305_843_009_213_693_952);
            assert(crate::round::round_frac(-(PI_NUM as int), 4 * PI_DEN as int, crate::types::Dir::Nearest)
                == Rat::from_raw_spec(-1_811_004_864_519_280_709i64, 2_305_843_009_213_693_952)) by (compute);
            assert(crate::round::round_frac(-(PI_NUM as int), 4 * PI_DEN as int, crate::types::Dir::Nearest).n() < 0) by (compute);
        },
        (Q::NegInf, Q::NegInf) => {
            Rat::lemma_from_raw_spec_components(-339_563_412_097_365_133i64, 144_115_188_075_855_872);
            assert(crate::round::round_frac(-(3 * PI_NUM as int), 4 * PI_DEN as int, crate::types::Dir::Nearest)
                == Rat::from_raw_spec(-339_563_412_097_365_133i64, 144_115_188_075_855_872)) by (compute);
            assert(crate::round::round_frac(-(3 * PI_NUM as int), 4 * PI_DEN as int, crate::types::Dir::Nearest).n() < 0) by (compute);
        },
        _ => assert(false),
    }
}

/// The infinite-coordinate \`atan2\` targets lie in their mathematical quadrants.
pub proof fn lemma_atan2_inf_target_quadrant(y: Q, x: Q)
    requires
        y.spec_is_infinite(),
        x.spec_is_infinite(),
    ensures
        y == Q::PosInf && x == Q::PosInf ==> crate::model::q_lt_frac(atan2_inf_target(y, x), PI_NUM as int, 2 * PI_DEN as int),
        y == Q::PosInf && x == Q::NegInf ==> crate::model::q_lt_frac(atan2_inf_target(y, x), PI_NUM as int, PI_DEN as int)
            && crate::model::q_ge_frac(atan2_inf_target(y, x), PI_NUM as int, 2 * PI_DEN as int),
        y == Q::NegInf && x == Q::PosInf ==> crate::model::q_ge_frac(atan2_inf_target(y, x), -(PI_NUM as int), 2 * PI_DEN as int),
        y == Q::NegInf && x == Q::NegInf ==> crate::model::q_lt_frac(atan2_inf_target(y, x), -(PI_NUM as int), 2 * PI_DEN as int)
            && crate::model::q_ge_frac(atan2_inf_target(y, x), -(PI_NUM as int), PI_DEN as int),
{
    match (y, x) {
        (Q::PosInf, Q::PosInf) => {
            Rat::lemma_from_raw_spec_components(1_811_004_864_519_280_709, 2_305_843_009_213_693_952);
            assert(crate::round::round_frac(PI_NUM as int, 4 * PI_DEN as int, crate::types::Dir::Nearest)
                == Rat::from_raw_spec(1_811_004_864_519_280_709, 2_305_843_009_213_693_952)) by (compute);
            assert(crate::model::q_lt_frac(
                crate::round::round_frac(PI_NUM as int, 4 * PI_DEN as int, crate::types::Dir::Nearest), PI_NUM as int, 2 * PI_DEN as int)) by (compute);
        },
        (Q::PosInf, Q::NegInf) => {
            Rat::lemma_from_raw_spec_components(339_563_412_097_365_133, 144_115_188_075_855_872);
            assert(crate::round::round_frac(3 * PI_NUM as int, 4 * PI_DEN as int, crate::types::Dir::Nearest)
                == Rat::from_raw_spec(339_563_412_097_365_133, 144_115_188_075_855_872)) by (compute);
            assert(crate::model::q_lt_frac(crate::round::round_frac(3 * PI_NUM as int, 4 * PI_DEN as int, crate::types::Dir::Nearest), PI_NUM as int, PI_DEN as int)) by (compute);
            assert(crate::model::q_ge_frac(crate::round::round_frac(3 * PI_NUM as int, 4 * PI_DEN as int, crate::types::Dir::Nearest), PI_NUM as int, 2 * PI_DEN as int)) by (compute);
        },
        (Q::NegInf, Q::PosInf) => {
            Rat::lemma_from_raw_spec_components(-1_811_004_864_519_280_709i64, 2_305_843_009_213_693_952);
            assert(crate::round::round_frac(-(PI_NUM as int), 4 * PI_DEN as int, crate::types::Dir::Nearest)
                == Rat::from_raw_spec(-1_811_004_864_519_280_709i64, 2_305_843_009_213_693_952)) by (compute);
            assert(crate::model::q_ge_frac(
                crate::round::round_frac(-(PI_NUM as int), 4 * PI_DEN as int, crate::types::Dir::Nearest), -(PI_NUM as int), 2 * PI_DEN as int)) by (compute);
        },
        (Q::NegInf, Q::NegInf) => {
            Rat::lemma_from_raw_spec_components(-339_563_412_097_365_133i64, 144_115_188_075_855_872);
            assert(crate::round::round_frac(-(3 * PI_NUM as int), 4 * PI_DEN as int, crate::types::Dir::Nearest)
                == Rat::from_raw_spec(-339_563_412_097_365_133i64, 144_115_188_075_855_872)) by (compute);
            assert(crate::model::q_lt_frac(crate::round::round_frac(-(3 * PI_NUM as int), 4 * PI_DEN as int, crate::types::Dir::Nearest), -(PI_NUM as int), 2 * PI_DEN as int)) by (compute);
            assert(crate::model::q_ge_frac(crate::round::round_frac(-(3 * PI_NUM as int), 4 * PI_DEN as int, crate::types::Dir::Nearest), -(PI_NUM as int), PI_DEN as int)) by (compute);
        },
        _ => assert(false),
    }
}

/// `round(num · 2^63 / den)`, for `|x| <= EXP_ARG_LIMIT`; fits `i128`.
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
        assert(crate::model::abs_int((x.n()) * (crate::fx::FX_ONE as int)) <= 405828369621610135552
            * (x.d())) by (nonlinear_arith)
            requires
                crate::model::abs_int(x.n()) <= (EXP_ARG_LIMIT as int) * x.d(),
                x.d() > 0,
                (crate::fx::FX_ONE as int) == 9223372036854775808,
                (EXP_ARG_LIMIT as int) == 44,
        ;
    }
    let raw: i128 = x.numerator() as i128;
    let d: i128 = x.denominator() as i128;
    let neg: bool = raw < 0;
    let m: i128 = if neg {
        0 - raw
    } else {
        raw
    };
    let scaled: i128 = m * crate::fx::FX_ONE;
    let q: i128 = scaled / d;
    let rem: i128 = scaled % d;
    proof {
        assert(m as int >= 0);
        lemma_fx_to_grid_decomposition(m as int, d as int, q as int, rem as int);
        assert((q as int) <= 405828369621610135552) by (nonlinear_arith)
            requires
                (m as int) * (crate::fx::FX_ONE as int)
                    == (q as int) * (d as int) + (rem as int),
                (rem as int) >= 0,
                (d as int) >= 1,
                (m as int) * (crate::fx::FX_ONE as int)
                    <= 405828369621610135552 * (d as int),
        ;
        assert((rem as int) * 2 < 9223372036854775808) by (nonlinear_arith)
            requires
                (rem as int) < (d as int),
                (d as int) <= crate::model::max_mag(),
                crate::model::max_mag() < 4611686018427387904,
        ;
    }
    let twice_rem: i128 = rem * 2;
    let round_up: bool = twice_rem > d || (twice_rem == d && q % 2 == 1);
    let rounded: i128 = if round_up { q + 1 } else { q };
    proof {
        assert((rounded as int) == if 2 * (rem as int) > (d as int)
            || (2 * (rem as int) == (d as int) && (q as int) % 2 == 1) {
            (q as int) + 1
        } else {
            q as int
        });
        lemma_fx_to_grid_nearest(m as int, d as int, q as int, rem as int, rounded as int);
        lemma_fx_to_grid_ties_even(m as int, d as int, q as int, rem as int, rounded as int);
        lemma_fx_to_grid_bound(
            m as int,
            d as int,
            q as int,
            rem as int,
            rounded as int,
            neg,
        );
    }
    if neg {
        0 - rounded
    } else {
        rounded
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


/// A small grid value as a `Q`: `v · 2^-63`, for `|v| <= 2^63`.
///
/// The mantissa logarithm is at most `ln 2 / 2` in magnitude, so a shift of two
/// brings it inside `i64` with the denominator at `2^61`, and the pair is then
/// an ordinary `Rat`.
fn fx_small_to_q(v: i128) -> (r: Q)
    requires
        crate::model::abs_int(v as int) <= 10350000000000000000i128 as int,
    ensures
        r.wf(),
{
    proof {
        crate::model::lemma_max_mag_pow2();
    }
    let neg: bool = v < 0;
    let m: i128 = if neg {
        0 - v
    } else {
        v
    };
    // Round to the `2^-61` grid, which is where the crate's own contract sits.
    let q: i128 = (m + 2) / 4;
    proof {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod((m as int) + 2, 4int);
        vstd::arithmetic::div_mod::lemma_mod_bound((m as int) + 2, 4int);
        assert((q as int) <= 2600000000000000000) by (nonlinear_arith)
            requires
                ((m as int) + 2) == 4 * (q as int) + (((m as int) + 2) % 4),
                (((m as int) + 2) % 4) >= 0,
                (m as int) <= 10350000000000000000,
        ;
    }
    let num: i128 = if neg {
        0 - q
    } else {
        q
    };
    // `Q::new` is total: a numerator past the budget saturates rather than
    // failing, and this one is inside it whenever the caller's bound holds.
    Q::new(num as i64, 1i64 << 61)
}

impl Q {
    /// `e^self`. `PosSat` above `43.67` (where `e^x > MAX_MAG`), `0` below
    /// `-44`; `exp(NegSat)` is `Nan` because the image `(0, e^-MAX_MAG)` does
    /// not contain zero, whereas underflow of a `Number` is inside R3.
    /// Evaluated by [`crate::fx::fx_exp_reduced`] and reassembled here; the
    /// `m >= 62` branch keeps results between `2^61` and `MAX_MAG` numeric.
    ///
    /// Accuracy is measured, not proven.
    ///
    /// ```
    /// use the_q::Q;
    ///
    /// let e2 = Q::new(2, 1).exp();
    /// if let Q::Number(x) = e2 {
    ///     assert!((the_q::to_f64(x) - 7.38905609893065).abs() < 1e-9);
    /// } else {
    ///     panic!("expected a number");
    /// }
    /// assert_eq!(Q::new(100, 1).exp(), Q::PosSat);
    /// ```
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
                let lim: i128 = (EXP_ARG_LIMIT as i128) * (x.denominator() as i128);
                let axn: i128 = if x.numerator() < 0 {
                    0 - (x.numerator() as i128)
                } else {
                    x.numerator() as i128
                };
                if axn > lim {
                    return if x.numerator() > 0 {
                        Q::PosSat
                    } else {
                        Q::zero()
                    };
                }
                // The argument on the fixed-point grid. `|x| <= 44` and
                // `x.den >= 1`, thus the scaled numerator is inside `i128`.
                let xg: i128 = fx_to_grid(x);
                let (t, m) = crate::fx::fx_exp_reduced(xg);
                // The value is `t · 2^(m-63)` with `|t| <= 1.6 · 2^63`.
                if m >= 62 {
                    // `2^m` alone is outside the budget, but the value may
                    // not be: assemble it as an integer and let the budget
                    // decide. `m <= 66`, so the multiplier is at most 8.
                    let v: i128 = if m == 62 {
                        (t + 1) / 2
                    } else {
                        let pow: i128 = if m == 63 {
                            1
                        } else if m == 64 {
                            2
                        } else if m == 65 {
                            4
                        } else {
                            8
                        };
                        proof {
                            assert(crate::model::abs_int((t as int) * (pow as int))
                                <= 8 * (crate::fx::FX_T_MAX as int)) by (nonlinear_arith)
                                requires
                                    crate::model::abs_int(t as int) <= crate::fx::FX_T_MAX as int,
                                    1 <= pow as int <= 8,
                            ;
                        }
                        t * pow
                    };
                    let mm: i128 = crate::types::MAX_MAG as i128;
                    if v > mm {
                        Q::PosSat
                    } else if v < 0 - mm {
                        Q::NegSat
                    } else {
                        Q::new(v as i64, 1)
                    }
                } else if m <= -62 {
                    // Below `2^-62` everything rounds to zero. At `m == -62`
                    // the value is `fx_quarter(t) · 2^-123`, which rounds to
                    // `2^-61` exactly when `fx_quarter(t) > 2^61` (a tie at
                    // `2^61` goes to the even neighbour, zero).
                    let q4: i64 = fx_quarter(t);
                    if m == -62 && q4 > (1i64 << 61) {
                        Q::new(1, 1i64 << 61)
                    } else {
                        Q::zero()
                    }
                } else {
                    // A shift of two brings `t` inside the budget with the
                    // denominator at `2^61`.
                    let mant = Q::new(fx_quarter(t), 1i64 << 61);
                    Q::mul(pow2_q(m), mant)
                }
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

/// `atanh(z)` for `|z| <= 1/3`; the twentieth term at `1/3` is `3e-21`, below
/// the grid.
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

/// `e` by `Σ 1/n!`, independently of `exp`; the derivation of [`e`].
///
/// Public only because Verus's visibility rules require it; not part of the
/// semver-stable API. Bit-identical to [`e`] (see `e_is_the_series_value`).
///
/// ```
/// use the_q::transcendental::{e, e_series};
///
/// assert_eq!(e_series(), e());
/// ```
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
///
/// ```
/// use the_q::Q;
/// use the_q::transcendental::e;
///
/// if let Q::Number(x) = e() {
///     assert!((the_q::to_f64(x) - std::f64::consts::E).abs() < 1e-9);
/// } else {
///     panic!("expected a number");
/// }
/// ```
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
///
/// Public only because Verus's visibility rules require it; not part of the
/// semver-stable API. Bit-identical to [`ln2`] (see `ln2_is_the_series_value`).
///
/// ```
/// use the_q::transcendental::{ln2, ln2_series};
///
/// assert_eq!(ln2_series(), ln2());
/// ```
pub fn ln2_series() -> (r: Q)
    ensures
        r.wf(),
{
    Q::mul(Q::new(2, 1), atanh_series(Q::new(1, 3)))
}

/// `ln 2` as a literal; `ln2_is_the_series_value` checks it against
/// [`ln2_series`] bit for bit.
///
/// ```
/// use the_q::Q;
/// use the_q::transcendental::ln2;
///
/// if let Q::Number(x) = ln2() {
///     assert!((the_q::to_f64(x) - std::f64::consts::LN_2).abs() < 1e-9);
/// } else {
///     panic!("expected a number");
/// }
/// ```
pub fn ln2() -> (r: Q)
    ensures
        r.wf(),
{
    Q::new(399572145162582989, 576460752303423488)
}

impl Q {
    /// The natural logarithm. `ln(0)` is `NegInf`; negative and `PosSat` are
    /// `Nan`. Binary reduction to `m ∈ [1/2, 2]`, then
    /// `ln(m) = 2·atanh((m-1)/(m+1))` with `|argument| <= 1/3`, plus `k·ln 2`.
    ///
    /// ```
    /// use the_q::Q;
    ///
    /// assert_eq!(Q::one().ln(), Q::zero());
    /// assert_eq!(Q::zero().ln(), Q::NegInf);
    /// assert_eq!(Q::new(-1, 1).ln(), Q::Nan);
    /// ```
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
                //
                // Integers, not a quantised mantissa: near one the difference cancels the
                // leading bits, and a quantised mantissa has nothing under them.
                let (mn, md): (i64, i64) = match m {
                    Q::Number(r) => (r.numerator(), r.denominator()),
                    // Unreachable: halving and doubling a positive number
                    // toward `[1/2, 2]` cannot leave the representable range.
                    // Answering `Nan` keeps the function total without a proof
                    // about the loops above.
                    _ => {
                        return Q::Nan;
                    },
                };
                proof {
                    crate::model::lemma_max_mag_pow2();
                }
                // The near-one branch.
                //
                // The kernel's error is `2^-63` absolute, which is a large relative error
                // for a result near zero; within `2^-8` of one the exact rational path keeps
                // the low bits (see README for measured accuracy).
                let diff: i128 = (mn as i128) - (md as i128);
                let adiff: i128 = if diff < 0 {
                    0 - diff
                } else {
                    diff
                };
                let near_one: bool = up == 0 && down == 0 && adiff * 256 < (md as i128);
                let ln_m = if near_one {
                    let one = Q::one();
                    let z = Q::div(Q::sub(m, one), Q::add(m, one));
                    Q::mul(Q::new(2, 1), atanh_series(z))
                } else {
                    if mn <= 0 {
                        return Q::Nan;
                    }
                    let zg: i128 = crate::fx::fx_ratio_z(mn as i128, md as i128);
                    // `ln(m) = 2·atanh(z)`. The doubling happens in `Q` rather
                    // than on the grid, so the grid value stays inside the
                    // budget of the `Rat` it becomes.
                    Q::mul(Q::new(2, 1), fx_small_to_q(crate::fx::fx_atanh_series(zg)))
                };
                // k is the net number of doublings undone; `up` and `down` are
                // never both nonzero, so this cannot overflow an i64.
                let k = Q::sub(Q::new(up as i64, 1), Q::new(down as i64, 1));
                Q::add(ln_m, Q::mul(k, ln2()))
            },
        }
    }

    /// `self^e`; `pow_i32(a, -n)` is `recip(pow_u32(a, n))`, so `pow_i32(0, -1)`
    /// is `PosInf`.
    ///
    /// ```
    /// use the_q::Q;
    ///
    /// assert_eq!(Q::new(2, 1).pow_i32(3), Q::new(8, 1));
    /// assert_eq!(Q::zero().pow_i32(-1), Q::PosInf);
    /// ```
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

/// Terms of the `atan` series on `|z| <= 1/2`: the tail at `k = 28` is
/// `1.2e-19`, below the grid; the series converges only geometrically.
const ATAN_TERMS: u32 = 30;

/// Largest `|x|` that `sin`, `cos`, `tan` accept; beyond it they return `Nan`.
/// The reduction `x mod π/2` uses one word of `π`, so the reduced argument has
/// absolute error about `|x| · 2^-60`: `2^-40` at the limit, measured.
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

/// `π` by Machin, `16·atan(1/5) − 4·atan(1/239)`; the derivation of [`pi`].
///
/// Public only because Verus's visibility rules require it; not part of the
/// semver-stable API. Bit-identical to [`pi`] (see `pi_is_the_series_value`).
///
/// ```
/// use the_q::transcendental::{pi, pi_series};
///
/// assert_eq!(pi_series(), pi());
/// ```
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
///
/// ```
/// use the_q::Q;
/// use the_q::transcendental::pi;
///
/// if let Q::Number(x) = pi() {
///     assert!((the_q::to_f64(x) - std::f64::consts::PI).abs() < 1e-9);
/// } else {
///     panic!("expected a number");
/// }
/// ```
pub fn pi() -> (r: Q)
    ensures
        r.wf(),
{
    Q::new(PI_NUM, PI_DEN)
}

/// `π/2`.
///
/// ```
/// use the_q::Q;
/// use the_q::transcendental::{half_pi, pi};
///
/// assert_eq!(half_pi(), Q::div(pi(), Q::new(2, 1)));
/// ```
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
    /// The arctangent in `(-π/2, π/2)`; `atan(±∞) = ±π/2`, `atan(PosSat)` is
    /// `Nan`. Reduced by `|x| > 1 → π/2 − atan(1/x)` and
    /// `|x| > 1/2 → π/4 + atan((x−1)/(x+1))` to `|x| <= 1/2` before the series.
    ///
    /// ```
    /// use the_q::Q;
    /// use the_q::transcendental::half_pi;
    ///
    /// assert_eq!(Q::PosInf.atan(), half_pi());
    /// assert_eq!(Q::PosSat.atan(), Q::Nan);
    /// ```
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

    /// The sine. `Nan` for `|x| > 2^20` and for every special. Reduction
    /// `r = x − round(x / (π/2)) · π/2`, then the series selected by `n mod 4`.
    ///
    /// ```
    /// use the_q::Q;
    ///
    /// assert_eq!(Q::zero().sin(), Q::zero());
    /// assert_eq!(Q::new((1i64 << 20) + 1, 1).sin(), Q::Nan);
    /// ```
    pub fn sin(self) -> (r: Q)
        requires
            self.wf(),
        ensures
            r.wf(),
    {
        Q::sin_cos(self, false)
    }

    /// The cosine. Same domain and method as [`Q::sin`].
    ///
    /// ```
    /// use the_q::Q;
    ///
    /// assert_eq!(Q::zero().cos(), Q::one());
    /// assert_eq!(Q::new((1i64 << 20) + 1, 1).cos(), Q::Nan);
    /// ```
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
    ///
    /// ```
    /// use the_q::Q;
    ///
    /// assert_eq!(Q::zero().tan(), Q::zero());
    /// assert_eq!(Q::new((1i64 << 20) + 1, 1).tan(), Q::Nan);
    /// ```
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
///
/// Public only because Verus's visibility rules require it; not part of the
/// semver-stable API. Bit-identical to [`ln10`] (see `ln10_is_the_series_value`).
///
/// ```
/// use the_q::transcendental::{ln10, ln10_series};
///
/// assert_eq!(ln10_series(), ln10());
/// ```
pub fn ln10_series() -> (r: Q)
    ensures
        r.wf(),
{
    Q::new(10, 1).ln()
}

/// `ln 10` as a literal, checked against [`ln10_series`] by test.
///
/// ```
/// use the_q::Q;
/// use the_q::transcendental::ln10;
///
/// if let Q::Number(x) = ln10() {
///     assert!((the_q::to_f64(x) - std::f64::consts::LN_10).abs() < 1e-9);
/// } else {
///     panic!("expected a number");
/// }
/// ```
pub fn ln10() -> (r: Q)
    ensures
        r.wf(),
{
    Q::new(2654699869899991811, 1152921504606846976)
}

impl Q {
    /// The base-2 logarithm, as `ln(self) / ln(2)`.
    ///
    /// ```
    /// use the_q::Q;
    ///
    /// let l = Q::new(8, 1).log2();
    /// if let Q::Number(x) = l {
    ///     assert!((the_q::to_f64(x) - 3.0).abs() < 1e-9);
    /// } else {
    ///     panic!("expected a number");
    /// }
    /// ```
    pub fn log2(self) -> (r: Q)
        requires
            self.wf(),
        ensures
            r.wf(),
    {
        Q::div(self.ln(), ln2())
    }

    /// The base-10 logarithm, as `ln(self) / ln(10)`.
    ///
    /// ```
    /// use the_q::Q;
    ///
    /// let l = Q::new(100, 1).log10();
    /// if let Q::Number(x) = l {
    ///     assert!((the_q::to_f64(x) - 2.0).abs() < 1e-9);
    /// } else {
    ///     panic!("expected a number");
    /// }
    /// ```
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
    ///
    /// ```
    /// use the_q::Q;
    ///
    /// let l = Q::new(8, 1).log(Q::new(2, 1));
    /// if let Q::Number(x) = l {
    ///     assert!((the_q::to_f64(x) - 3.0).abs() < 1e-9);
    /// } else {
    ///     panic!("expected a number");
    /// }
    /// assert_eq!(Q::new(8, 1).log(Q::one()), Q::PosInf);
    /// ```
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
    ///
    /// Accuracy is measured, not proven; the result need not be the exact
    /// rational power.
    ///
    /// ```
    /// use the_q::Q;
    ///
    /// let r = Q::new(3, 1).exp2();
    /// if let Q::Number(x) = r {
    ///     assert!((the_q::to_f64(x) - 8.0).abs() < 1e-9);
    /// } else {
    ///     panic!("expected a number");
    /// }
    /// ```
    pub fn exp2(self) -> (r: Q)
        requires
            self.wf(),
        ensures
            r.wf(),
    {
        Q::mul(self, ln2()).exp()
    }

    /// `self^exponent` as `exp(exponent · ln(self))`: `Nan` for a negative base
    /// (use [`Q::pow_i32`] for integer exponents); `0^0` is `1`.
    ///
    /// ```
    /// use the_q::Q;
    ///
    /// let r = Q::new(2, 1).powf(Q::new(3, 1));
    /// if let Q::Number(x) = r {
    ///     assert!((the_q::to_f64(x) - 8.0).abs() < 1e-9);
    /// } else {
    ///     panic!("expected a number");
    /// }
    /// assert_eq!(Q::new(-1, 1).powf(Q::new(2, 1)), Q::Nan);
    /// ```
    pub fn powf(self, exponent: Q) -> (r: Q)
        requires
            self.wf(),
            exponent.wf(),
        ensures
            r.wf(),
            exponent.spec_is_zero() ==> r.spec_is_value(1, 1),
            self.spec_is_zero() && exponent.spec_signum() == Some(Sign::Positive)
                ==> r.spec_is_value(0, 1),
            self.spec_is_zero() && exponent.spec_signum() == Some(Sign::Negative)
                ==> r == Q::PosInf,
            self.spec_is_zero() && exponent.spec_is_nan() ==> r == Q::Nan,
    {
        if exponent.is_zero() {
            return Q::one();
        }
        if self.is_zero() {
            return match exponent.signum() {
                Some(Sign::Positive) => Q::zero(),
                Some(Sign::Negative) => Q::PosInf,
                Some(Sign::Zero) => Q::one(),
                None => Q::Nan,
            };
        }
        Q::mul(exponent, self.ln()).exp()
    }

    /// The cube root on the whole real line, as `±exp(ln|x| / 3)`.
    ///
    /// Accuracy is measured, not proven.
    ///
    /// ```
    /// use the_q::Q;
    ///
    /// let r = Q::new(8, 1).cbrt();
    /// if let Q::Number(x) = r {
    ///     assert!((the_q::to_f64(x) - 2.0).abs() < 1e-9);
    /// } else {
    ///     panic!("expected a number");
    /// }
    /// assert_eq!(Q::PosSat.cbrt(), Q::Nan);
    /// ```
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

    /// `sqrt(self² + other²)` as `|a|·sqrt(1 + (b/a)²)` with `a` the larger, so
    /// the square stays representable when `a² + b²` does not.
    ///
    /// ```
    /// use the_q::Q;
    ///
    /// assert_eq!(Q::new(3, 1).hypot(Q::new(4, 1)), Q::new(5, 1));
    /// assert_eq!(Q::zero().hypot(Q::zero()), Q::zero());
    /// ```
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

    /// `(e^x − e^-x) / 2`; beyond `|x| > 22` it is `±e^(|x| − ln 2)` to within the
    /// grid, which saturates cleanly instead of dividing a `PosSat` by two.
    ///
    /// ```
    /// use the_q::Q;
    ///
    /// assert_eq!(Q::zero().sinh(), Q::zero());
    /// assert_eq!(Q::new(100, 1).sinh(), Q::PosSat);
    /// ```
    pub fn sinh(self) -> (r: Q)
        requires
            self.wf(),
        ensures
            r.wf(),
    {
        match self {
            Q::Nan => Q::Nan,
            Q::PosInf => Q::PosInf,
            Q::NegInf => Q::NegInf,
            Q::PosSat => Q::PosSat,
            Q::NegSat => Q::NegSat,
            Q::Number(_) => {
                let lim = Q::new(HYP_ARG_LIMIT, 1);
                if Q::gt(self, lim) {
                    Q::sub(self, ln2()).exp()
                } else if Q::lt(self, lim.neg()) {
                    Q::sub(self.neg(), ln2()).exp().neg()
                } else {
                    Q::div(Q::sub(self.exp(), self.neg().exp()), Q::new(2, 1))
                }
            },
        }
    }

    /// The hyperbolic cosine, `(e^x + e^-x) / 2`, with the same large-argument
    /// path as [`Q::sinh`].
    ///
    /// ```
    /// use the_q::Q;
    ///
    /// assert_eq!(Q::zero().cosh(), Q::one());
    /// assert_eq!(Q::new(100, 1).cosh(), Q::PosSat);
    /// ```
    pub fn cosh(self) -> (r: Q)
        requires
            self.wf(),
        ensures
            r.wf(),
    {
        match self {
            Q::Nan => Q::Nan,
            Q::PosInf | Q::NegInf => Q::PosInf,
            Q::PosSat | Q::NegSat => Q::PosSat,
            Q::Number(_) => {
                let lim = Q::new(HYP_ARG_LIMIT, 1);
                if Q::gt(self.abs(), lim) {
                    Q::sub(self.abs(), ln2()).exp()
                } else {
                    Q::div(Q::add(self.exp(), self.neg().exp()), Q::new(2, 1))
                }
            },
        }
    }

    /// `sinh / cosh`; `±1` beyond `|x| >= 22` (where `1 − |tanh x| < 2^-62`) and
    /// for the infinite and saturated states.
    ///
    /// ```
    /// use the_q::Q;
    ///
    /// assert_eq!(Q::zero().tanh(), Q::zero());
    /// assert_eq!(Q::new(100, 1).tanh(), Q::one());
    /// assert_eq!(Q::PosInf.tanh(), Q::one());
    /// ```
    pub fn tanh(self) -> (r: Q)
        requires
            self.wf(),
        ensures
            r.wf(),
    {
        match self {
            Q::Nan => Q::Nan,
            Q::PosInf | Q::PosSat => Q::one(),
            Q::NegInf | Q::NegSat => Q::one().neg(),
            Q::Number(_) => {
                let lim = Q::new(HYP_ARG_LIMIT, 1);
                if Q::ge(self, lim) {
                    Q::one()
                } else if Q::le(self, lim.neg()) {
                    Q::one().neg()
                } else {
                    Q::div(self.sinh(), self.cosh())
                }
            },
        }
    }

    /// The arcsine, in `[-π/2, π/2]`.
    ///
    /// The result is `Nan` outside `[-1, 1]`, where there is no real answer.
    /// The function computes the endpoints directly. The identity below divides
    /// by zero at those two points.
    ///
    /// ```
    /// use the_q::Q;
    /// use the_q::transcendental::half_pi;
    ///
    /// assert_eq!(Q::one().asin(), half_pi());
    /// assert_eq!(Q::new(2, 1).asin(), Q::Nan);
    /// ```
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
    ///
    /// ```
    /// use the_q::Q;
    ///
    /// assert_eq!(Q::one().acos(), Q::zero());
    /// let r = Q::zero().acos();
    /// if let Q::Number(x) = r {
    ///     assert!((the_q::to_f64(x) - std::f64::consts::FRAC_PI_2).abs() < 1e-9);
    /// } else {
    ///     panic!("expected a number");
    /// }
    /// ```
    pub fn acos(self) -> (r: Q)
        requires
            self.wf(),
        ensures
            r.wf(),
    {
        Q::sub(Q::div(pi(), Q::new(2, 1)), self.asin())
    }

    /// The angle of `(x, y)` in `(-π, π]`; `atan2(0, 0)` is `Nan`.
    ///
    /// ```
    /// use the_q::Q;
    ///
    /// assert_eq!(Q::zero().atan2(Q::one()), Q::zero());
    /// assert_eq!(Q::zero().atan2(Q::zero()), Q::Nan);
    /// ```
    pub fn atan2(self, x: Q) -> (r: Q)
        requires
            self.wf(),
            x.wf(),
        ensures
            r.wf(),
            self.spec_is_infinite() && x.spec_is_infinite()
                ==> r == Q::Number(atan2_inf_target(self, x)),
    {
        let y = self;
        let zero = Q::zero();
        let p = pi();
        let hp = Q::div(p, Q::new(2, 1));
        if y.is_nan() || x.is_nan() {
            return Q::Nan;
        }
        if y.is_infinite() && x.is_infinite() {
            return Q::Number(atan2_inf_target_exec(y, x));
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

#[cfg(test)]
mod tests {
    use super::fx_to_grid;
    use crate::Rat;

    #[test]
    fn fx_to_grid_rounds_nearest_ties_even() {
        assert_eq!(fx_to_grid(Rat::zero()), 0);
        assert_eq!(fx_to_grid(Rat::one()), 9_223_372_036_854_775_808);
        assert_eq!(fx_to_grid(Rat::neg_one()), -9_223_372_036_854_775_808);
        assert_eq!(
            fx_to_grid(Rat::new(1, 2).unwrap()),
            4_611_686_018_427_387_904
        );
        assert_eq!(
            fx_to_grid(Rat::new(1, 3).unwrap()),
            3_074_457_345_618_258_603
        );
        assert_eq!(
            fx_to_grid(Rat::new(-1, 3).unwrap()),
            -3_074_457_345_618_258_603
        );
    }
}
