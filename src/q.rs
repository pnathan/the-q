//! The public `Rat` API: constructors, arithmetic, comparison, predicates.
//!
//! Each operation computes its exact result in `i128` and passes that result
//! to [`crate::round::round_frac_exec`]. That function canonicalises the pair,
//! and rounds it only when the exact result does not fit the budget. No
//! operation in this module can panic. Division by zero is a precondition that
//! the caller discharges, and each `i128` intermediate is proven in range
//! (V2).
//!
//! ## Widths
//!
//! | operation | widest intermediate | bound under I2 |
//! |---|---|---|
//! | `mul` | `num1·num2`, `den1·den2` | `< 2^124` |
//! | `add`/`sub` | `num1·den2 ± num2·den1` | `< 2^125` |
//! | `div` | `num1·den2`, `den1·num2` | `< 2^124` |
//! | `cmp` | `num1·den2` vs `num2·den1` | `< 2^124` |
//!
//! `i128::MAX` is `2^127 - 1`, thus each column has at least two bits of
//! headroom. With a `2^63` budget the `add` row reaches `2^127` and overflows.
//! The budget is `2^62` for that reason.

use verus_builtin_macros::verus;

#[allow(unused_imports)]
use verus_builtin::*;
#[allow(unused_imports)]
use vstd::prelude::*;

#[allow(unused_imports)]
use crate::gcd::*;
#[allow(unused_imports)]
use crate::model::*;
#[allow(unused_imports)]
use crate::round::*;
use crate::types::{Dir, MAX_DEC_PLACES, MAX_MAG, Rat};

verus! {

// ---------------------------------------------------------------------------
// Exact numerators and denominators of the four operations, in ghost form
// ---------------------------------------------------------------------------

/// The exact numerator of `a + b`.
pub open spec fn add_n(a: Rat, b: Rat) -> int {
    a.n() * b.d() + b.n() * a.d()
}

/// The exact numerator of `a - b`.
pub open spec fn sub_n(a: Rat, b: Rat) -> int {
    a.n() * b.d() - b.n() * a.d()
}

/// The exact numerator of `a * b`.
pub open spec fn mul_n(a: Rat, b: Rat) -> int {
    a.n() * b.n()
}

/// The common denominator of `a + b`, `a - b` and `a * b`.
pub open spec fn prod_d(a: Rat, b: Rat) -> int {
    a.d() * b.d()
}

/// The exact numerator of `a / b`, sign-normalised so the denominator is
/// positive.
pub open spec fn div_n(a: Rat, b: Rat) -> int {
    if b.n() > 0 {
        a.n() * b.d()
    } else {
        -(a.n() * b.d())
    }
}

/// The exact denominator of `a / b`, always positive.
pub open spec fn div_d(a: Rat, b: Rat) -> int {
    if b.n() > 0 {
        a.d() * b.n()
    } else {
        -(a.d() * b.n())
    }
}

/// `num` with the sign of a negative `den` folded onto it.
///
/// `round_frac` takes a positive denominator, thus [`Rat::new_rounded`]
/// normalises the sign before it rounds. The pair that it rounds is
/// `(signed_den_num(num, den), abs_int(den))`, and its postconditions use that
/// pair. The pair has the same value as `num / den`. The normalisation is
/// necessary: rounding `-3 / -4` in direction `Down` means rounding `3 / 4`
/// down, and not `-3 / 4` down.
pub open spec fn signed_den_num(num: int, den: int) -> int {
    if den < 0 {
        -num
    } else {
        num
    }
}

// ---------------------------------------------------------------------------
// Constructors
// ---------------------------------------------------------------------------

impl Rat {
    /// `0`.
    pub fn zero() -> (r: Rat)
        ensures
            r.wf(),
            r.n() == 0,
            r.d() == 1,
    {
        proof {
            crate::round::lemma_gcd_one();
            lemma_max_mag_pow2();
        }
        Rat { num: 0, den: 1 }
    }

    /// `1`.
    pub fn one() -> (r: Rat)
        ensures
            r.wf(),
            r.n() == 1,
            r.d() == 1,
    {
        proof {
            crate::round::lemma_gcd_one();
            lemma_max_mag_pow2();
        }
        Rat { num: 1, den: 1 }
    }

    /// `-1`.
    pub fn neg_one() -> (r: Rat)
        ensures
            r.wf(),
            r.n() == -1,
            r.d() == 1,
    {
        Rat::one().neg()
    }

    /// The integer `i` as a rational.
    ///
    /// `None` when `|i| > MAX_MAG` — in particular for `i64::MIN`, whose
    /// absolute value is not an `i64` at all.
    pub fn from_int(i: i64) -> (r: Option<Rat>)
        ensures
            r.is_some() ==> {
                &&& r.unwrap().wf()
                &&& r.unwrap().n() == i as int
                &&& r.unwrap().d() == 1
            },
            r.is_none() ==> abs_int(i as int) > crate::model::max_mag(),
    {
        if i > MAX_MAG || i < -MAX_MAG {
            None
        } else {
            proof {
                crate::round::lemma_gcd_one();
                lemma_max_mag_pow2();
            }
            Some(Rat { num: i, den: 1 })
        }
    }

    /// The exact rational `num / den`, canonicalised.
    ///
    /// The result is `None` when `den == 0`, and also when the reduced form
    /// does not fit the budget. The second case needs `|num|` or `|den|` above
    /// `2^62 - 1`, which is the top bit of the `i64` range. This behaviour is
    /// an intentional departure from a literal reading of the specification,
    /// which states that each `i64` pair fits after reduction.
    /// `Rat::new(i64::MAX, 1)` is a counterexample to that statement.
    /// [`Rat::new_rounded`] is the total variant, which rounds instead.
    pub fn new(num: i64, den: i64) -> (r: Option<Rat>)
        ensures
            den == 0 ==> r.is_none(),
            r.is_some() ==> {
                &&& r.unwrap().wf()
                &&& q_is(r.unwrap(), num as int, den as int)
            },
            // Completeness. Without this clause an implementation that returns
            // `None` for each nonzero denominator satisfies the contract.
            // `q_is` states the answer when an answer exists, and no other
            // clause states that an answer exists.
            //
            // The condition uses the unreduced pair. The tight form, "`None`
            // exactly when the reduced form does not fit", needs the caller to
            // compute the gcd. A caller can check both components against the
            // budget at the call site, and reduction only makes them smaller.
            (den != 0 && abs_int(num as int) <= max_mag() && abs_int(den as int) <= max_mag())
                ==> r.is_some(),
    {
        if den == 0 {
            return None;
        }
        let mut n: i128 = num as i128;
        let mut d: i128 = den as i128;
        let neg: bool = d < 0;
        if neg {
            n = 0 - n;
            d = 0 - d;
        }
        let g: i128 = gcd_abs_i128(n, d);
        let rn: i128 = n / g;
        let rd: i128 = d / g;
        let arn: i128 = if rn < 0 {
            0 - rn
        } else {
            rn
        };
        if arn <= MAX_MAG as i128 && rd <= MAX_MAG as i128 {
            proof {
                lemma_max_mag_pow2();
                crate::round::lemma_reduce_exact(n as int, d as int);
                crate::gcd::lemma_gcd_reduce_coprime(abs_int(n as int) as nat, d as nat);
                crate::round::lemma_reduce_abs(n as int, d as int);
                // I1's zero clause: `gcd(0, d) == d`, so a zero numerator
                // reduces the denominator all the way to one.
                if num == 0 {
                    crate::gcd::lemma_gcd_zero(d as nat);
                    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
                        d as int,
                        d as int,
                        1,
                        0,
                    );
                }
                // n == rn·g and d == rd·g, and (n, d) is (num, den) up to a
                // shared sign flip, so rn/rd is num/den as a value either way.
                lemma_new_value(
                    num as int,
                    den as int,
                    n as int,
                    d as int,
                    rn as int,
                    rd as int,
                    g as int,
                    neg,
                );
                // The zero clause of I1 on the returned pair: `rn == 0` forces
                // `rd == 1`. The step above gives `rd == d` when `num == 0`,
                // and `d == 1` follows from `lemma_gcd_zero` and
                // `lemma_fundamental_div_mod_converse`. This separate step
                // keeps the proof stable against unrelated additions to the
                // module. The `saturation` module header describes that
                // effect.
                assert(rn == 0 ==> rd == 1);
            }
            Some(Rat { num: rn as i64, den: rd as i64 })
        } else {
            proof {
                // Completeness, discharged contrapositively on this path only.
                // `g == gcd_int(n, d)`, thus `rn` and `rd` are `red_num` and
                // `red_den`, and reduction never enlarges either component.
                // This branch thus means that the pair of the caller is outside
                // the budget.
                //
                // These two facts also prove the clause above the `if`, but
                // that position destabilises the `rn == 0 ==> rd == 1` step in
                // the other branch. The `saturation` module header describes
                // that effect.
                lemma_max_mag_pow2();
                crate::round::lemma_reduce_shrinks(n as int, d as int);
            }
            None
        }
    }

    /// The rational `num / den`, rounded to the budget if it does not fit.
    ///
    /// `None` **iff** `den == 0`.
    ///
    /// The function normalises the sign onto the numerator before it rounds.
    /// A negative `den` thus rounds the same value in the same direction, and
    /// not the mirrored one. `signed_den_num` holds that convention, and the
    /// postconditions below use it.
    pub fn new_rounded(num: i64, den: i64, dir: Dir) -> (r: Option<Rat>)
        ensures
            r.is_none() <==> den == 0,
            r.is_some() ==> r.unwrap().wf(),
            // The value pin. This clause fixes the result completely and does
            // not only describe properties of it. The R2 and R3 clauses below
            // follow from this clause. They are stated so that a caller does
            // not derive them.
            r.is_some() ==> r.unwrap() == round_frac(
                signed_den_num(num as int, den as int),
                abs_int(den as int),
                dir,
            ),
            // R2 and R3, both guarded on `!saturated`. That guard is the scope
            // of the rounding contract of the crate. `new_rounded` accepts each
            // `i64` pair, and `(i64::MAX, 1)` is above the magnitude ceiling,
            // thus an unguarded R3 is false here. `from_decimal` discharges the
            // guard for its callers, because its inputs cannot saturate.
            (r.is_some() && !saturated(signed_den_num(num as int, den as int), abs_int(
                den as int,
            ))) ==> {
                // R2: each directed mode lands on its own side of the exact
                // value. R3: the per-operation error bound of the crate,
                // against the exact input rational.
                &&& dir == Dir::Down ==> q_le_frac(
                    r.unwrap(),
                    signed_den_num(num as int, den as int),
                    abs_int(den as int),
                )
                &&& dir == Dir::Up ==> q_ge_frac(
                    r.unwrap(),
                    signed_den_num(num as int, den as int),
                    abs_int(den as int),
                )
                &&& within_error_bound(
                    r.unwrap(),
                    signed_den_num(num as int, den as int),
                    abs_int(den as int),
                )
            },
    {
        if den == 0 {
            return None;
        }
        let mut n: i128 = num as i128;
        let mut d: i128 = den as i128;
        if d < 0 {
            n = 0 - n;
            d = 0 - d;
        }
        proof {
            lemma_pow2_124();
            lemma_pow2_126();
            if !saturated(n as int, d as int) {
                crate::round::lemma_r2_r3_directed(n as int, d as int, dir);
            }
        }
        Some(round_frac_exec(n, d, dir))
    }

    /// The exact decimal `mantissa · 10^-dec_places`, e.g. `(85, 2)` is `0.85`.
    ///
    /// This constructor is the primary ingestion path of the crate.
    /// Reliabilities, competences and weights arrive as short decimals, and
    /// this constructor converts them with no rounding.
    ///
    /// `None` when `dec_places > 18` (the scale factor would leave the budget)
    /// or `|mantissa| > MAX_MAG`.
    pub fn from_decimal(mantissa: i64, dec_places: u8) -> (r: Option<Rat>)
        ensures
            r.is_some() ==> r.unwrap().wf(),
            dec_places > MAX_DEC_PLACES ==> r.is_none(),
            // The value of the result, and not only its well-formedness. The
            // README calls this constructor the primary ingestion path, and the
            // doc comment states that the conversion is exact. This clause puts
            // both claims in the verified contract and pins the value of
            // `from_decimal(85, 2)`.
            r.is_some() ==> q_is(r.unwrap(), mantissa as int, pow10(dec_places as nat)),
            // The existence condition. A caller can check both guards, and
            // together they are the failure set. Inside them `Rat::new` cannot
            // fail, by its completeness clause.
            r.is_some() <==> (dec_places <= MAX_DEC_PLACES && abs_int(mantissa as int)
                <= max_mag()),
    {
        if dec_places > MAX_DEC_PLACES {
            return None;
        }
        if mantissa > MAX_MAG || mantissa < -MAX_MAG {
            return None;
        }
        let scale: i64 = pow10_i64(dec_places);
        proof {
            // `scale` is in `[1, 10^18]` and `max_mag()` is `2^62 - 1`, about
            // `4.6 · 10^18`, so the scale factor is always inside the budget
            // and `Rat::new`'s completeness precondition is met.
            lemma_max_mag_pow2();
        }
        Rat::new(mantissa, scale)
    }
}

/// `10^n` for `n <= 18`, as a literal table.
///
/// The function uses a table and not a loop. A loop needs an invariant that
/// relates the accumulator to `10^(n-i)`, and a bound that proves that the next
/// multiplication cannot overflow. That is three proof obligations and one
/// lemma for the same result. Nineteen literals are clear to the verifier and
/// to the reader.
pub fn pow10_i64(n: u8) -> (r: i64)
    requires
        n <= MAX_DEC_PLACES,
    ensures
        1 <= r <= 1000000000000000000,
        // The table is `10^n`, and this clause states that property. Without
        // it `from_decimal` can describe its result only as well-formed. The
        // proof is nineteen unfoldings of a linear recursion, which is cheap.
        // The literal pins of `pow2` need lemmas, because nonlinear goals
        // consume them. These pins appear in linear goals only.
        r == pow10(n as nat),
{
    reveal_with_fuel(pow10, 20);
    match n {
        0 => 1,
        1 => 10,
        2 => 100,
        3 => 1000,
        4 => 10000,
        5 => 100000,
        6 => 1000000,
        7 => 10000000,
        8 => 100000000,
        9 => 1000000000,
        10 => 10000000000,
        11 => 100000000000,
        12 => 1000000000000,
        13 => 10000000000000,
        14 => 100000000000000,
        15 => 1000000000000000,
        16 => 10000000000000000,
        17 => 100000000000000000,
        _ => 1000000000000000000,
    }
}

// ---------------------------------------------------------------------------
// Arithmetic
// ---------------------------------------------------------------------------

impl Rat {
    /// `a + b`, rounded in direction `dir`.
    pub fn add_dir(a: Rat, b: Rat, dir: Dir) -> (r: Rat)
        requires
            a.wf(),
            b.wf(),
        ensures
            r.wf(),
            r == round_frac(add_n(a, b), prod_d(a, b), dir),
            exact_path(add_n(a, b), prod_d(a, b)) ==> q_is(r, add_n(a, b), prod_d(a, b)),
            !saturated(add_n(a, b), prod_d(a, b)) ==> within_error_bound(
                r,
                add_n(a, b),
                prod_d(a, b),
            ),
    {
        proof {
            lemma_op_widths(a, b);
        }
        let n: i128 = (a.num as i128) * (b.den as i128) + (b.num as i128) * (a.den as i128);
        let d: i128 = (a.den as i128) * (b.den as i128);
        let r = round_frac_exec(n, d, dir);
        proof {
            if exact_path(add_n(a, b), prod_d(a, b)) {
                crate::round::lemma_r1_identity(add_n(a, b), prod_d(a, b), dir);
            }
            if !saturated(add_n(a, b), prod_d(a, b)) {
                crate::round::lemma_r3_error(add_n(a, b), prod_d(a, b), dir);
            }
        }
        r
    }

    /// `a - b`, rounded in direction `dir`.
    pub fn sub_dir(a: Rat, b: Rat, dir: Dir) -> (r: Rat)
        requires
            a.wf(),
            b.wf(),
        ensures
            r.wf(),
            r == round_frac(sub_n(a, b), prod_d(a, b), dir),
            exact_path(sub_n(a, b), prod_d(a, b)) ==> q_is(r, sub_n(a, b), prod_d(a, b)),
            !saturated(sub_n(a, b), prod_d(a, b)) ==> within_error_bound(
                r,
                sub_n(a, b),
                prod_d(a, b),
            ),
    {
        proof {
            lemma_op_widths(a, b);
        }
        let n: i128 = (a.num as i128) * (b.den as i128) - (b.num as i128) * (a.den as i128);
        let d: i128 = (a.den as i128) * (b.den as i128);
        let r = round_frac_exec(n, d, dir);
        proof {
            if exact_path(sub_n(a, b), prod_d(a, b)) {
                crate::round::lemma_r1_identity(sub_n(a, b), prod_d(a, b), dir);
            }
            if !saturated(sub_n(a, b), prod_d(a, b)) {
                crate::round::lemma_r3_error(sub_n(a, b), prod_d(a, b), dir);
            }
        }
        r
    }

    /// `a * b`, rounded in direction `dir`.
    pub fn mul_dir(a: Rat, b: Rat, dir: Dir) -> (r: Rat)
        requires
            a.wf(),
            b.wf(),
        ensures
            r.wf(),
            r == round_frac(mul_n(a, b), prod_d(a, b), dir),
            exact_path(mul_n(a, b), prod_d(a, b)) ==> q_is(r, mul_n(a, b), prod_d(a, b)),
            !saturated(mul_n(a, b), prod_d(a, b)) ==> within_error_bound(
                r,
                mul_n(a, b),
                prod_d(a, b),
            ),
    {
        proof {
            lemma_op_widths(a, b);
        }
        let n: i128 = (a.num as i128) * (b.num as i128);
        let d: i128 = (a.den as i128) * (b.den as i128);
        let r = round_frac_exec(n, d, dir);
        proof {
            if exact_path(mul_n(a, b), prod_d(a, b)) {
                crate::round::lemma_r1_identity(mul_n(a, b), prod_d(a, b), dir);
            }
            if !saturated(mul_n(a, b), prod_d(a, b)) {
                crate::round::lemma_r3_error(mul_n(a, b), prod_d(a, b), dir);
            }
        }
        r
    }

    /// `a / b`, rounded in direction `dir`.
    ///
    /// Division by zero is a precondition and not a runtime error. The caller
    /// discharges `!b.is_zero()` statically, thus this function has no panic
    /// path.
    pub fn div_dir(a: Rat, b: Rat, dir: Dir) -> (r: Rat)
        requires
            a.wf(),
            b.wf(),
            b.n() != 0,
        ensures
            r.wf(),
            r == round_frac(div_n(a, b), div_d(a, b), dir),
            exact_path(div_n(a, b), div_d(a, b)) ==> q_is(r, div_n(a, b), div_d(a, b)),
            !saturated(div_n(a, b), div_d(a, b)) ==> within_error_bound(
                r,
                div_n(a, b),
                div_d(a, b),
            ),
    {
        proof {
            lemma_op_widths(a, b);
            crate::model::lemma_pow2_124();
            crate::model::lemma_pow2_126();
            // The sign of the divisor is the sign of its numerator, because
            // `a.d() > 0`. The flip below thus gives `div_d(a, b) > 0`.
            assert(b.n() > 0 ==> a.d() * b.n() > 0) by (nonlinear_arith)
                requires
                    a.d() > 0,
            ;
            assert(b.n() < 0 ==> a.d() * b.n() < 0) by (nonlinear_arith)
                requires
                    a.d() > 0,
            ;
        }
        let mut n: i128 = (a.num as i128) * (b.den as i128);
        let mut d: i128 = (a.den as i128) * (b.num as i128);
        if d < 0 {
            n = 0 - n;
            d = 0 - d;
        }
        let r = round_frac_exec(n, d, dir);
        proof {
            if exact_path(div_n(a, b), div_d(a, b)) {
                crate::round::lemma_r1_identity(div_n(a, b), div_d(a, b), dir);
            }
            if !saturated(div_n(a, b), div_d(a, b)) {
                crate::round::lemma_r3_error(div_n(a, b), div_d(a, b), dir);
            }
        }
        r
    }

    /// `a + b`, round to nearest (ties to even).
    ///
    /// The error is a half grid step and not a whole one, thus this operation
    /// achieves `B = 62`. That is one bit better than the `B = 61` of the
    /// directed modes. See `round::lemma_r3_error_nearest`.
    pub fn add(a: Rat, b: Rat) -> (r: Rat)
        requires
            a.wf(),
            b.wf(),
        ensures
            r.wf(),
            r == round_frac(add_n(a, b), prod_d(a, b), Dir::Nearest),
            exact_path(add_n(a, b), prod_d(a, b)) ==> q_is(r, add_n(a, b), prod_d(a, b)),
            !saturated(add_n(a, b), prod_d(a, b)) ==> crate::model::within_error_bound_nearest(
                r,
                add_n(a, b),
                prod_d(a, b),
            ),
    {
        let r = Rat::add_dir(a, b, Dir::Nearest);
        proof {
            lemma_op_widths(a, b);
            if !saturated(add_n(a, b), prod_d(a, b)) {
                crate::round::lemma_r3_error_nearest(add_n(a, b), prod_d(a, b));
            }
        }
        r
    }

    /// `a - b`, round to nearest (ties to even). Achieves `B = 62`, as `add`
    /// does.
    pub fn sub(a: Rat, b: Rat) -> (r: Rat)
        requires
            a.wf(),
            b.wf(),
        ensures
            r.wf(),
            r == round_frac(sub_n(a, b), prod_d(a, b), Dir::Nearest),
            exact_path(sub_n(a, b), prod_d(a, b)) ==> q_is(r, sub_n(a, b), prod_d(a, b)),
            !saturated(sub_n(a, b), prod_d(a, b)) ==> crate::model::within_error_bound_nearest(
                r,
                sub_n(a, b),
                prod_d(a, b),
            ),
    {
        let r = Rat::sub_dir(a, b, Dir::Nearest);
        proof {
            lemma_op_widths(a, b);
            if !saturated(sub_n(a, b), prod_d(a, b)) {
                crate::round::lemma_r3_error_nearest(sub_n(a, b), prod_d(a, b));
            }
        }
        r
    }

    /// `a * b`, round to nearest (ties to even). Achieves `B = 62`, as `add`
    /// does.
    pub fn mul(a: Rat, b: Rat) -> (r: Rat)
        requires
            a.wf(),
            b.wf(),
        ensures
            r.wf(),
            r == round_frac(mul_n(a, b), prod_d(a, b), Dir::Nearest),
            exact_path(mul_n(a, b), prod_d(a, b)) ==> q_is(r, mul_n(a, b), prod_d(a, b)),
            !saturated(mul_n(a, b), prod_d(a, b)) ==> crate::model::within_error_bound_nearest(
                r,
                mul_n(a, b),
                prod_d(a, b),
            ),
    {
        let r = Rat::mul_dir(a, b, Dir::Nearest);
        proof {
            lemma_op_widths(a, b);
            if !saturated(mul_n(a, b), prod_d(a, b)) {
                crate::round::lemma_r3_error_nearest(mul_n(a, b), prod_d(a, b));
            }
        }
        r
    }

    /// `a / b`, round to nearest (ties to even). Requires `!b.is_zero()`.
    /// Achieves `B = 62`, as `add` does.
    pub fn div(a: Rat, b: Rat) -> (r: Rat)
        requires
            a.wf(),
            b.wf(),
            b.n() != 0,
        ensures
            r.wf(),
            r == round_frac(div_n(a, b), div_d(a, b), Dir::Nearest),
            exact_path(div_n(a, b), div_d(a, b)) ==> q_is(r, div_n(a, b), div_d(a, b)),
            !saturated(div_n(a, b), div_d(a, b)) ==> crate::model::within_error_bound_nearest(
                r,
                div_n(a, b),
                div_d(a, b),
            ),
    {
        let r = Rat::div_dir(a, b, Dir::Nearest);
        proof {
            lemma_op_widths(a, b);
            assert(b.n() > 0 ==> a.d() * b.n() > 0) by (nonlinear_arith)
                requires
                    a.d() > 0,
            ;
            assert(b.n() < 0 ==> a.d() * b.n() < 0) by (nonlinear_arith)
                requires
                    a.d() > 0,
            ;
            if !saturated(div_n(a, b), div_d(a, b)) {
                crate::round::lemma_r3_error_nearest(div_n(a, b), div_d(a, b));
            }
        }
        r
    }

    /// `a + b`, or `None` if the exact sum is too large in magnitude to be
    /// represented at all (`|a + b| > MAX_MAG`).
    pub fn checked_add(a: Rat, b: Rat) -> (r: Option<Rat>)
        requires
            a.wf(),
            b.wf(),
        ensures
            r.is_none() <==> saturated(add_n(a, b), prod_d(a, b)),
            r.is_some() ==> r.unwrap() == round_frac(add_n(a, b), prod_d(a, b), Dir::Nearest),
            r.is_some() ==> r.unwrap().wf(),
    {
        proof {
            lemma_op_widths(a, b);
            crate::model::lemma_pow2_126();
        }
        if magnitude_fits_exec(add_n_exec(a, b), prod_d_exec(a, b)) {
            Some(Rat::add(a, b))
        } else {
            None
        }
    }

    /// `a * b`, or `None` if the exact product is too large in magnitude.
    pub fn checked_mul(a: Rat, b: Rat) -> (r: Option<Rat>)
        requires
            a.wf(),
            b.wf(),
        ensures
            r.is_none() <==> saturated(mul_n(a, b), prod_d(a, b)),
            r.is_some() ==> r.unwrap() == round_frac(mul_n(a, b), prod_d(a, b), Dir::Nearest),
            r.is_some() ==> r.unwrap().wf(),
    {
        proof {
            lemma_op_widths(a, b);
            crate::model::lemma_pow2_126();
        }
        if magnitude_fits_exec(mul_n_exec(a, b), prod_d_exec(a, b)) {
            Some(Rat::mul(a, b))
        } else {
            None
        }
    }

    /// `a - b`, or `None` if the exact difference is too large in magnitude.
    pub fn checked_sub(a: Rat, b: Rat) -> (r: Option<Rat>)
        requires
            a.wf(),
            b.wf(),
        ensures
            r.is_none() <==> saturated(sub_n(a, b), prod_d(a, b)),
            r.is_some() ==> r.unwrap() == round_frac(sub_n(a, b), prod_d(a, b), Dir::Nearest),
            r.is_some() ==> r.unwrap().wf(),
    {
        proof {
            lemma_op_widths(a, b);
            crate::model::lemma_pow2_126();
        }
        if magnitude_fits_exec(sub_n_exec(a, b), prod_d_exec(a, b)) {
            Some(Rat::sub(a, b))
        } else {
            None
        }
    }

    /// `a / b`, or `None` if the exact quotient is too large in magnitude.
    /// Requires `!b.is_zero()`.
    ///
    /// Division saturates on the magnitude ceiling that `add`, `sub` and `mul`
    /// use. For example, `(MAX_MAG/1) / (1/MAX_MAG)` is far above that ceiling.
    /// This function thus completes the `checked_*` family.
    pub fn checked_div(a: Rat, b: Rat) -> (r: Option<Rat>)
        requires
            a.wf(),
            b.wf(),
            b.n() != 0,
        ensures
            r.is_none() <==> saturated(div_n(a, b), div_d(a, b)),
            r.is_some() ==> r.unwrap() == round_frac(div_n(a, b), div_d(a, b), Dir::Nearest),
            r.is_some() ==> r.unwrap().wf(),
    {
        proof {
            lemma_op_widths(a, b);
            crate::model::lemma_pow2_126();
        }
        if magnitude_fits_exec(div_n_exec(a, b), div_d_exec(a, b)) {
            Some(Rat::div(a, b))
        } else {
            None
        }
    }

    /// `-a`. Always exact: the budget is symmetric in sign.
    pub fn neg(self) -> (r: Rat)
        requires
            self.wf(),
        ensures
            r.wf(),
            r.n() == -self.n(),
            r.d() == self.d(),
    {
        proof {
            lemma_max_mag_pow2();
            assert(gcd_int(-self.n(), self.d()) == gcd_int(self.n(), self.d()));
        }
        Rat { num: 0 - self.num, den: self.den }
    }

    /// `|a|`. Always exact.
    pub fn abs(self) -> (r: Rat)
        requires
            self.wf(),
        ensures
            r.wf(),
            r.n() == abs_int(self.n()),
            r.d() == self.d(),
    {
        if self.num < 0 {
            self.neg()
        } else {
            self
        }
    }

    /// `1 / a`. Always exact. The operation swaps the numerator and the
    /// denominator, and I2 is symmetric between them.
    pub fn recip(self) -> (r: Rat)
        requires
            self.wf(),
            self.n() != 0,
        ensures
            r.wf(),
            r.n() * self.n() > 0,
            q_is_recip(r, self),
    {
        proof {
            lemma_max_mag_pow2();
        }
        if self.num > 0 {
            proof {
                assert(gcd_int(self.d(), self.n()) == gcd_int(self.n(), self.d())) by {
                    lemma_gcd_sym(abs_int(self.n()) as nat, self.d() as nat);
                }
                assert(self.d() * self.n() > 0) by (nonlinear_arith)
                    requires
                        self.d() > 0,
                        self.n() > 0,
                ;
            }
            Rat { num: self.den, den: self.num }
        } else {
            proof {
                assert(gcd_int(-self.d(), -self.n()) == gcd_int(self.n(), self.d())) by {
                    lemma_gcd_sym(abs_int(self.n()) as nat, self.d() as nat);
                }
                assert((-self.d()) * self.n() > 0) by (nonlinear_arith)
                    requires
                        self.d() > 0,
                        self.n() < 0,
                ;
                assert((-self.d()) * self.n() == self.d() * (-self.n())) by (nonlinear_arith);
            }
            Rat { num: 0 - self.den, den: 0 - self.num }
        }
    }

    /// `a^e` by repeated multiplication, as a left fold. This module has no
    /// rational-exponent power.
    pub fn pow_u32(self, e: u32) -> (r: Rat)
        requires
            self.wf(),
        ensures
            r.wf(),
    {
        let mut acc = Rat::one();
        let mut i: u32 = 0;
        while i < e
            invariant
                acc.wf(),
                self.wf(),
                i <= e,
            decreases e - i,
        {
            acc = Rat::mul(acc, self);
            i = i + 1;
        }
        acc
    }
}

/// `r == 1 / q`, division-free.
pub open spec fn q_is_recip(r: Rat, q: Rat) -> bool {
    r.n() * q.n() == q.d() * r.d()
}

/// `gcd` is symmetric.
pub proof fn lemma_gcd_sym(a: nat, b: nat)
    ensures
        crate::model::gcd_nat(a, b) == crate::model::gcd_nat(b, a),
{
    crate::gcd::lemma_gcd_divides(a, b);
    crate::gcd::lemma_gcd_divides(b, a);
    crate::gcd::lemma_gcd_greatest(a, b, crate::model::gcd_nat(b, a) as int);
    crate::gcd::lemma_gcd_greatest(b, a, crate::model::gcd_nat(a, b) as int);
    if a > 0 || b > 0 {
        crate::gcd::lemma_gcd_pos(a, b);
        crate::gcd::lemma_gcd_pos(b, a);
        crate::model::lemma_divides_le(
            crate::model::gcd_nat(a, b) as int,
            crate::model::gcd_nat(b, a) as int,
        );
        crate::model::lemma_divides_le(
            crate::model::gcd_nat(b, a) as int,
            crate::model::gcd_nat(a, b) as int,
        );
    }
}

/// All four operations' intermediates are inside the `i128` range, and inside
/// the input bounds `round_frac_exec` requires.
pub proof fn lemma_op_widths(a: Rat, b: Rat)
    requires
        a.wf(),
        b.wf(),
    ensures
        // Literal forms. These discharge the `i128` overflow checks at the
        // call sites. `pow2(124)` is an opaque recursive term for the solver,
        // thus a bound in that form proves nothing about an `i128`.
        abs_int(a.n() * b.d()) < 21267647932558653966460912964485513216,
        abs_int(b.n() * a.d()) < 21267647932558653966460912964485513216,
        // The two cross terms, in the order that `div_dir` uses. Both orders
        // are necessary. `abs_int` applies to the product, thus the solver
        // must otherwise commute the factors inside an opaque application.
        abs_int(a.d() * b.n()) < 21267647932558653966460912964485513216,
        abs_int(a.d() * b.n()) <= pow2(124),
        abs_int(a.n() * b.d()) <= pow2(124),
        abs_int(a.n() * b.n()) < 21267647932558653966460912964485513216,
        abs_int(a.d() * b.d()) < 21267647932558653966460912964485513216,
        abs_int(add_n(a, b)) < 42535295865117307932921825928971026432,
        abs_int(sub_n(a, b)) < 42535295865117307932921825928971026432,
        abs_int(mul_n(a, b)) < 42535295865117307932921825928971026432,
        a.d() * b.d() > 0,
        a.d() > 0,
        b.d() > 0,
        // `pow2` forms, for `round_frac_exec`'s preconditions.
        abs_int(a.d() * b.d()) <= pow2(124),
        abs_int(add_n(a, b)) < pow2(126),
        abs_int(sub_n(a, b)) < pow2(126),
        abs_int(mul_n(a, b)) < pow2(126),
{
    lemma_mul_in_i128(a.n(), b.d());
    lemma_mul_in_i128(b.n(), a.d());
    lemma_mul_in_i128(a.d(), b.n());
    lemma_mul_in_i128(a.n(), b.n());
    lemma_mul_in_i128(a.d(), b.d());
    lemma_pow2_124();
    lemma_pow2_126();
    assert(a.d() * b.d() > 0) by (nonlinear_arith)
        requires
            a.d() > 0,
            b.d() > 0,
    ;
}

/// The reduced pair denotes the original fraction, whichever way the sign was
/// normalised.
pub proof fn lemma_new_value(
    num: int,
    den: int,
    n: int,
    d: int,
    rn: int,
    rd: int,
    g: int,
    neg: bool,
)
    requires
        den != 0,
        g > 0,
        n == rn * g,
        d == rd * g,
        neg ==> (n == -num && d == -den),
        !neg ==> (n == num && d == den),
    ensures
        rn * den == num * rd,
{
    if neg {
        assert(den == -(rd * g) && num == -(rn * g));
        assert(rn * den == -((rn * rd) * g)) by (nonlinear_arith)
            requires
                den == -(rd * g),
        ;
        assert(num * rd == -((rn * rd) * g)) by (nonlinear_arith)
            requires
                num == -(rn * g),
        ;
    } else {
        assert(den == rd * g && num == rn * g);
        assert(rn * den == (rn * rd) * g) by (nonlinear_arith)
            requires
                den == rd * g,
        ;
        assert(num * rd == (rn * rd) * g) by (nonlinear_arith)
            requires
                num == rn * g,
        ;
    }
}

/// Exec mirrors of the ghost numerators, used by the `checked_*` variants.
pub fn add_n_exec(a: Rat, b: Rat) -> (r: i128)
    requires
        a.wf(),
        b.wf(),
    ensures
        r as int == add_n(a, b),
{
    proof {
        lemma_op_widths(a, b);
        lemma_pow2_126();
    }
    (a.num as i128) * (b.den as i128) + (b.num as i128) * (a.den as i128)
}

/// Exec mirror of `sub_n`.
pub fn sub_n_exec(a: Rat, b: Rat) -> (r: i128)
    requires
        a.wf(),
        b.wf(),
    ensures
        r as int == sub_n(a, b),
{
    proof {
        lemma_op_widths(a, b);
        lemma_pow2_126();
    }
    (a.num as i128) * (b.den as i128) - (b.num as i128) * (a.den as i128)
}

/// Exec mirror of `mul_n`.
pub fn mul_n_exec(a: Rat, b: Rat) -> (r: i128)
    requires
        a.wf(),
        b.wf(),
    ensures
        r as int == mul_n(a, b),
{
    proof {
        lemma_op_widths(a, b);
        lemma_pow2_126();
    }
    (a.num as i128) * (b.num as i128)
}

/// Exec mirror of `prod_d`.
pub fn prod_d_exec(a: Rat, b: Rat) -> (r: i128)
    requires
        a.wf(),
        b.wf(),
    ensures
        r as int == prod_d(a, b),
        r > 0,
{
    proof {
        lemma_op_widths(a, b);
        lemma_pow2_126();
    }
    (a.den as i128) * (b.den as i128)
}

/// Exec mirror of `div_n`: sign-normalised the same way [`Rat::div_dir`]
/// computes it, so it pairs with [`div_d_exec`].
pub fn div_n_exec(a: Rat, b: Rat) -> (r: i128)
    requires
        a.wf(),
        b.wf(),
        b.n() != 0,
    ensures
        r as int == div_n(a, b),
{
    proof {
        lemma_op_widths(a, b);
        lemma_pow2_126();
        assert(b.n() > 0 ==> a.d() * b.n() > 0) by (nonlinear_arith)
            requires
                a.d() > 0,
        ;
        assert(b.n() < 0 ==> a.d() * b.n() < 0) by (nonlinear_arith)
            requires
                a.d() > 0,
        ;
    }
    let mut n: i128 = (a.num as i128) * (b.den as i128);
    let d: i128 = (a.den as i128) * (b.num as i128);
    if d < 0 {
        n = 0 - n;
    }
    n
}

/// Exec mirror of `div_d`: always positive, the denominator [`div_n_exec`]
/// pairs with.
pub fn div_d_exec(a: Rat, b: Rat) -> (r: i128)
    requires
        a.wf(),
        b.wf(),
        b.n() != 0,
    ensures
        r as int == div_d(a, b),
        r > 0,
{
    proof {
        lemma_op_widths(a, b);
        lemma_pow2_126();
        assert(b.n() > 0 ==> a.d() * b.n() > 0) by (nonlinear_arith)
            requires
                a.d() > 0,
        ;
        assert(b.n() < 0 ==> a.d() * b.n() < 0) by (nonlinear_arith)
            requires
                a.d() > 0,
        ;
    }
    let mut d: i128 = (a.den as i128) * (b.num as i128);
    if d < 0 {
        d = 0 - d;
    }
    d
}

/// The magnitude test, without ever forming `MAX_MAG · d`.
pub fn magnitude_fits_exec(n: i128, d: i128) -> (r: bool)
    requires
        d > 0,
        // Negating `n` below is only safe away from `i128::MIN`. Every caller
        // passes a numerator bounded by `lemma_op_widths`, well inside this.
        abs_int(n as int) < crate::round::num_input_bound(),
    ensures
        r <==> magnitude_fits(n as int, d as int),
{
    proof {
        crate::model::lemma_pow2_126();
    }
    let m: i128 = if n < 0 {
        0 - n
    } else {
        n
    };
    let ip: i128 = m / d;
    let fr: i128 = m % d;
    proof {
        crate::round::lemma_magnitude_test(m as int, d as int, ip as int, fr as int);
    }
    ip < MAX_MAG as i128 || (ip == MAX_MAG as i128 && fr == 0)
}

// ---------------------------------------------------------------------------
// Comparison and predicates — all exact, no epsilon, total
// ---------------------------------------------------------------------------

impl Rat {
    /// Three-way comparison: `-1`, `0`, `1`.
    ///
    /// Exact, by `i128` cross-multiplication. `ℚ` is totally ordered, which is
    /// a genuine upgrade over `f64`'s `PartialOrd`: there is no `NaN`, so there
    /// are no incomparable pairs and no need for `partial_cmp` to return
    /// `None`.
    pub fn compare(a: Rat, b: Rat) -> (r: i32)
        requires
            a.wf(),
            b.wf(),
        ensures
            r == 0 <==> q_eq(a, b),
            r < 0 <==> q_lt(a, b),
            r > 0 <==> q_lt(b, a),
    {
        proof {
            lemma_op_widths(a, b);
        }
        let l: i128 = (a.num as i128) * (b.den as i128);
        let r: i128 = (b.num as i128) * (a.den as i128);
        if l < r {
            -1
        } else if l > r {
            1
        } else {
            0
        }
    }

    /// `a == b`. Because `Rat` is canonical this is also structural equality.
    pub fn eq_q(a: Rat, b: Rat) -> (r: bool)
        requires
            a.wf(),
            b.wf(),
        ensures
            r <==> q_eq(a, b),
    {
        Rat::compare(a, b) == 0
    }

    /// `a < b`.
    pub fn lt(a: Rat, b: Rat) -> (r: bool)
        requires
            a.wf(),
            b.wf(),
        ensures
            r <==> q_lt(a, b),
    {
        Rat::compare(a, b) < 0
    }

    /// `a <= b`.
    pub fn le(a: Rat, b: Rat) -> (r: bool)
        requires
            a.wf(),
            b.wf(),
        ensures
            r <==> q_le(a, b),
    {
        Rat::compare(a, b) <= 0
    }

    /// `a > b`.
    pub fn gt(a: Rat, b: Rat) -> (r: bool)
        requires
            a.wf(),
            b.wf(),
        ensures
            r <==> q_lt(b, a),
    {
        Rat::compare(a, b) > 0
    }

    /// `a >= b`.
    pub fn ge(a: Rat, b: Rat) -> (r: bool)
        requires
            a.wf(),
            b.wf(),
        ensures
            r <==> q_le(b, a),
    {
        Rat::compare(a, b) >= 0
    }

    /// `a == 0`.
    pub fn is_zero(&self) -> (r: bool)
        requires
            self.wf(),
        ensures
            r <==> self.n() == 0,
    {
        self.num == 0
    }

    /// `a == 1`.
    pub fn is_one(&self) -> (r: bool)
        requires
            self.wf(),
        ensures
            r <==> self.n() == self.d(),
    {
        proof {
            // `n == d` makes `n` a common divisor of `|n|` and `d`, so it
            // divides their gcd, which `wf` pins at 1 — forcing `n == 1`.
            if self.n() == self.d() {
                crate::model::lemma_divides_basic(self.n());
                crate::gcd::lemma_gcd_greatest(
                    abs_int(self.n()) as nat,
                    self.d() as nat,
                    self.n(),
                );
                crate::model::lemma_divides_le(self.n(), 1);
            }
        }
        self.num == 1 && self.den == 1
    }

    /// `-1`, `0` or `1` according to the sign.
    pub fn signum(&self) -> (r: i32)
        requires
            self.wf(),
        ensures
            r == 0 <==> self.n() == 0,
            r < 0 <==> self.n() < 0,
            r > 0 <==> self.n() > 0,
    {
        if self.num < 0 {
            -1
        } else if self.num > 0 {
            1
        } else {
            0
        }
    }

    /// `0 <= a <= 1`.
    ///
    /// The consuming engine checks this constantly on beliefs, disbeliefs and
    /// uncertainties, so it is a first-class predicate rather than two
    /// comparisons.
    pub fn in_unit_interval(&self) -> (r: bool)
        requires
            self.wf(),
        ensures
            r <==> (self.n() >= 0 && self.n() <= self.d()),
    {
        self.num >= 0 && self.num <= self.den
    }

    /// The smaller of `a` and `b`. Exact.
    pub fn min(a: Rat, b: Rat) -> (r: Rat)
        requires
            a.wf(),
            b.wf(),
        ensures
            r.wf(),
            r == a || r == b,
            q_le(r, a),
            q_le(r, b),
            // ...and *which* argument. Without these the contract constrains
            // the result without naming it, leaving the connection between
            // "the contract pins a unique answer" and "this function returns
            // it" to a reader rather than to the prover.
            q_le(a, b) ==> r == a,
            !q_le(a, b) ==> r == b,
    {
        if Rat::le(a, b) {
            a
        } else {
            b
        }
    }

    /// The larger of `a` and `b`. Exact.
    pub fn max(a: Rat, b: Rat) -> (r: Rat)
        requires
            a.wf(),
            b.wf(),
        ensures
            r.wf(),
            r == a || r == b,
            q_le(a, r),
            q_le(b, r),
            // See `Rat::min`: these name the result rather than bounding it.
            q_le(a, b) ==> r == b,
            !q_le(a, b) ==> r == a,
    {
        if Rat::le(a, b) {
            b
        } else {
            a
        }
    }

    /// `a` clamped into `[lo, hi]`. Exact. Requires `lo <= hi`.
    pub fn clamp(a: Rat, lo: Rat, hi: Rat) -> (r: Rat)
        requires
            a.wf(),
            lo.wf(),
            hi.wf(),
            q_le(lo, hi),
        ensures
            r.wf(),
            r == a || r == lo || r == hi,
            q_le(lo, r),
            q_le(r, hi),
            // ...and *which* of the three.
            //
            // The four clauses above do not pin the result: for `lo < a < hi`
            // the value `lo` satisfies every one of them, so a `clamp` that
            // ignored `a` entirely and always returned `lo` would verify. That
            // is the same defect the extended `Q::clamp` had, and the same one
            // the old `isqrt_i64` postcondition had — a contract wide enough to
            // admit a wrong answer. It was found by proving the extended
            // version's contract categorical, failing, and checking whether the
            // kernel shared the weakness. It did.
            (q_le(lo, a) && q_le(a, hi)) ==> r == a,
            !q_le(lo, a) ==> r == lo,
            !q_le(a, hi) ==> r == hi,
    {
        proof {
            lemma_le_trans(lo, hi, a);
            // `a < lo <= hi` gives `a <= hi`, which makes the "returns `hi`"
            // clause vacuous on the `lo` branch.
            lemma_le_trans(a, lo, hi);
        }
        if Rat::lt(a, lo) {
            lo
        } else if Rat::lt(hi, a) {
            hi
        } else {
            a
        }
    }
}

/// `<=` is transitive on well-formed `Rat`.
pub proof fn lemma_le_trans(a: Rat, b: Rat, c: Rat)
    requires
        a.wf(),
        b.wf(),
        c.wf(),
    ensures
        (q_le(a, b) && q_le(b, c)) ==> q_le(a, c),
{
    if q_le(a, b) && q_le(b, c) {
        assert(a.n() * c.d() <= c.n() * a.d()) by (nonlinear_arith)
            requires
                a.d() > 0,
                b.d() > 0,
                c.d() > 0,
                a.n() * b.d() <= b.n() * a.d(),
                b.n() * c.d() <= c.n() * b.d(),
        ;
    }
}

} // verus!

// ---------------------------------------------------------------------------
// Standard trait impls
//
// These are thin, total delegations to the verified functions above. Verus does
// not model the `core` comparison traits, so they are marked `external`: they
// cannot be called from verified code, and verified code never needs them.
// They are enumerated in TRUSTED.md.
// ---------------------------------------------------------------------------

#[cfg_attr(verus_keep_ghost, verifier::external)]
impl PartialOrd for Rat {
    fn partial_cmp(&self, other: &Rat) -> Option<core::cmp::Ordering> {
        Some(<Rat as Ord>::cmp(self, other))
    }
}

#[cfg_attr(verus_keep_ghost, verifier::external)]
impl Ord for Rat {
    fn cmp(&self, other: &Rat) -> core::cmp::Ordering {
        // Delegate to the verified `Rat::compare` (proven against the ghost
        // order in `verus!` above) rather than reimplementing the
        // cross-multiplication here. This impl only maps its `-1`/`0`/`1`
        // onto `Ordering`.
        Rat::compare(*self, *other).cmp(&0)
    }
}

#[cfg_attr(verus_keep_ghost, verifier::external)]
impl core::ops::Add for Rat {
    type Output = Rat;

    fn add(self, rhs: Rat) -> Rat {
        Rat::add(self, rhs)
    }
}

#[cfg_attr(verus_keep_ghost, verifier::external)]
impl core::ops::Sub for Rat {
    type Output = Rat;

    fn sub(self, rhs: Rat) -> Rat {
        Rat::sub(self, rhs)
    }
}

#[cfg_attr(verus_keep_ghost, verifier::external)]
impl core::ops::Mul for Rat {
    type Output = Rat;

    fn mul(self, rhs: Rat) -> Rat {
        Rat::mul(self, rhs)
    }
}

#[cfg_attr(verus_keep_ghost, verifier::external)]
impl core::ops::Neg for Rat {
    type Output = Rat;

    fn neg(self) -> Rat {
        Rat::neg(self)
    }
}
