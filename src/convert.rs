//! The crate's edges: `f64` in and out, `Display`, `FromStr`, `serde`.
//!
//! Two functions touch a float and both are `external_body` (`TRUSTED.md`):
//! [`f64_decompose`] extracts the IEEE-754 fields, and [`to_f64`] is for
//! display only. Everything between is verified integer arithmetic: an `f64`
//! is `±m · 2^e`, so [`from_parts_dir`] builds the exact integer pair and hands
//! it to the same rounder every operation uses, and its contract pins the
//! result to `round_frac` of that pair.

use verus_builtin_macros::verus;

#[allow(unused_imports)]
use verus_builtin::*;
#[allow(unused_imports)]
use vstd::prelude::*;

#[allow(unused_imports)]
use crate::model::*;
#[allow(unused_imports)]
use crate::round::*;
use crate::types::{Dir, MAX_DECIMAL_MANTISSA, MAX_DECIMAL_SCALE, Rat};

verus! {

/// The IEEE-754 fields of a finite float, `(negative, mantissa, exponent)`;
/// `None` for NaN and infinities. TRUSTED: Verus has no model of `to_bits`.
#[verifier::external_body]
pub fn f64_decompose(v: f64) -> (r: Option<(bool, u64, i32)>)
    ensures
        r.is_some() ==> {
            let t = r.unwrap();
            &&& t.1 <= 9007199254740992u64  // 2^53
            &&& -1074 <= t.2 <= 971
        },
{
    let bits: u64 = v.to_bits();
    let neg: bool = (bits >> 63) != 0;
    let raw_exp: u64 = (bits >> 52) & 0x7ff;
    let frac: u64 = bits & 0x000f_ffff_ffff_ffff;
    if raw_exp == 0x7ff {
        // NaN or +/- infinity.
        return None;
    }
    if raw_exp == 0 {
        // Subnormal (and zero): value == frac * 2^-1074.
        Some((neg, frac, -1074))
    } else {
        // Normal: value == (2^52 + frac) * 2^(raw_exp - 1075).
        Some((neg, frac + 0x0010_0000_0000_0000u64, raw_exp as i32 - 1075))
    }
}

/// Convert an `f64` to a `Rat`, rounding in direction `dir`. `None` on NaN,
/// infinity, or `|v| > 2^61`. Below `2^-62` the result is the endpoint of the
/// first grid cell on the rounding side.
///
/// No postcondition can mention `v`: Verus has no model of `f64`. The contract
/// lives on [`from_parts_dir`]; this is its composition with [`f64_decompose`].
pub fn from_f64_dir(v: f64, dir: Dir) -> (r: Option<Rat>)
    ensures
        r.is_some() ==> r.unwrap().wf(),
{
    match f64_decompose(v) {
        None => None,
        Some((neg, mant, e)) => from_parts_dir(neg, mant, e, dir),
    }
}

/// The exact numerator of the value an IEEE-754 decomposition denotes:
/// `(-1)^neg · mant · 2^e`, with the `2^e` folded in when `e >= 0`.
pub open spec fn parts_num(neg: bool, mant: u64, e: i32) -> int {
    let m = if neg {
        -(mant as int)
    } else {
        mant as int
    };
    if e >= 0 {
        m * pow2(e as nat)
    } else {
        m
    }
}

/// The exact denominator of the same value, always positive.
pub open spec fn parts_den(e: i32) -> int {
    if e >= 0 {
        1int
    } else {
        pow2((-e) as nat)
    }
}

/// The verified core of [`from_f64_dir`]: `(neg, mant, e)` to a `Rat`.
///
/// The result is pinned to `round_frac` of the exact rational the triple
/// denotes, with R2 and R3 restated; the sub-grid branch (`2^s`, `s > 124`)
/// is covered by `round::lemma_round_frac_subgrid`. The `requires` is ghost and
/// this function is `pub`, so the body re-checks the bounds and returns `None`
/// outside them rather than overflow for an unverified caller.
pub fn from_parts_dir(neg: bool, mant: u64, e: i32, dir: Dir) -> (r: Option<Rat>)
    requires
        mant <= 9007199254740992u64,
        -1074 <= e <= 971,
    ensures
        r.is_some() ==> r.unwrap().wf(),
        // The value pin, over the *decomposed* rational.
        r.is_some() ==> r.unwrap() == round_frac(parts_num(neg, mant, e), parts_den(e), dir),
        // R2 and R3, guarded on `!saturated`, exactly as the crate's rounding
        // contract is scoped. This function discharges the guard for every
        // value it accepts rather than assumes it. It returns `None` above
        // `2^61`, so every value with a result is far inside the ceiling.
        r.is_some() ==> !saturated(parts_num(neg, mant, e), parts_den(e)),
        (r.is_some() && dir == Dir::Down) ==> q_le_frac(
            r.unwrap(),
            parts_num(neg, mant, e),
            parts_den(e),
        ),
        (r.is_some() && dir == Dir::Up) ==> q_ge_frac(
            r.unwrap(),
            parts_num(neg, mant, e),
            parts_den(e),
        ),
        r.is_some() ==> within_error_bound(
            r.unwrap(),
            parts_num(neg, mant, e),
            parts_den(e),
        ),
        // Completeness: the documented magnitude restriction is the *only*
        // reason this returns `None`.
        r.is_none() ==> abs_int(parts_num(neg, mant, e)) > pow2(61) * parts_den(e),
{
    // The `requires` above, enforced for callers Verus never sees. This branch
    // is dead under verification. The postconditions below are therefore
    // unweakened by it.
    if mant > 9007199254740992u64 || e < -1074 || e > 971 {
        return None;
    }
    if mant == 0 {
        proof {
            if e >= 0 {
                assert(parts_num(neg, mant, e) == 0) by (nonlinear_arith)
                    requires
                        parts_num(neg, mant, e) == 0 * pow2(e as nat),
                ;
            }
            assert(parts_den(e) > 0) by {
                lemma_pow2_pos((-e) as nat);
            }
            lemma_r2_r3_directed(parts_num(neg, mant, e), parts_den(e), dir);
            assert(gcd_int(0, 1) == 1) by {
                reveal_with_fuel(gcd_nat, 3);
            }
            Rat::lemma_from_raw_spec_wf(0, 1);
        }
        return Some(Rat::from_raw_parts(0, 1));
    }
    proof {
        lemma_pow2_61();
        lemma_pow2_62();
        lemma_pow2_124();
        lemma_pow2_126();
    }
    if e >= 0 {
        proof {
            lemma_pow2_pos(e as nat);
            // `|±mant · 2^e| == mant · 2^e`. Every branch below needs this
            // fact. It is a fact about `abs_int` of a product, so it is
            // established here rather than assumed inside a nonlinear block.
            let m = if neg {
                -(mant as int)
            } else {
                mant as int
            };
            lemma_abs_mul_pos(m, pow2(e as nat));
            assert(abs_int(m) == mant as int);
            assert(abs_int(parts_num(neg, mant, e)) == (mant as int) * pow2(e as nat));
        }
        if e > 64 {
            proof {
                // `mant >= 1` and `e >= 65`, so the value is at least `2^65`.
                // The postcondition needs a *strict* excess over `2^61`, so the
                // proof goes through `2^62`. Monotonicity alone gives only
                // `<=`.
                lemma_pow2_mono(62nat, e as nat);
                lemma_pow2_pos(61nat);
                lemma_pow2_pos(e as nat);
                assert(pow2(62) == 2 * pow2(61));
                assert(abs_int(parts_num(neg, mant, e)) >= pow2(e as nat))
                    by (nonlinear_arith)
                    requires
                        abs_int(parts_num(neg, mant, e)) == (mant as int) * pow2(e as nat),
                        mant >= 1,
                        pow2(e as nat) > 0,
                ;
                assert(parts_den(e) == 1);
                assert(abs_int(parts_num(neg, mant, e)) > pow2(61) * parts_den(e))
                    by (nonlinear_arith)
                    requires
                        abs_int(parts_num(neg, mant, e)) >= pow2(e as nat),
                        pow2(62) <= pow2(e as nat),
                        pow2(62) == 2 * pow2(61),
                        pow2(61) > 0,
                        parts_den(e) == 1,
                ;
            }
            return None;
        }
        let p: i128 = pow2_i128(e as u32);
        proof {
            // mant <= 2^53 and p == 2^e <= 2^64, so the product is at most
            // 2^117, far inside i128.
            lemma_pow2_mono(e as nat, 64nat);
            lemma_pow2_64();
            assert((mant as int) * (p as int) <= 9007199254740992int
                * 18446744073709551616int) by (nonlinear_arith)
                requires
                    0 <= mant <= 9007199254740992int,
                    0 < p <= 18446744073709551616int,
            ;
        }
        let mag: i128 = (mant as i128) * p;
        proof {
            assert(abs_int(parts_num(neg, mant, e)) == mag as int) by (nonlinear_arith)
                requires
                    abs_int(parts_num(neg, mant, e)) == (mant as int) * pow2(e as nat),
                    mag as int == (mant as int) * (p as int),
                    p as int == pow2(e as nat),
            ;
        }
        if mag > 2305843009213693952i128 {
            // > 2^61
            return None;
        }
        let n: i128 = if neg {
            0 - mag
        } else {
            mag
        };
        proof {
            assert(pow2(0) == 1);
            // `-(mant · 2^e) == (-mant) · 2^e`. The code applies the sign to
            // the product, and the spec applies it to the mantissa.
            assert(-((mant as int) * pow2(e as nat)) == (-(mant as int)) * pow2(e as nat))
                by (nonlinear_arith);
            assert(n as int == parts_num(neg, mant, e));
            assert(parts_den(e) == 1);
            // Inside `2^61`, so nowhere near the `2^62 - 1` ceiling.
            assert(!saturated(n as int, 1int)) by (nonlinear_arith)
                requires
                    abs_int(n as int) <= pow2(61),
                    max_mag() == pow2(62) - 1,
                    pow2(62) == 2 * pow2(61),
                    pow2(61) > 0,
            ;
            lemma_r2_r3_directed(n as int, 1int, dir);
        }
        Some(round_frac_exec(n, 1, dir))
    } else if e >= -124 {
        let s: u32 = (0 - e) as u32;
        let d: i128 = pow2_i128(s);
        let n: i128 = if neg {
            0 - (mant as i128)
        } else {
            mant as i128
        };
        proof {
            // d == 2^s with s <= 124, which is exactly the denominator bound
            // `round_frac_exec` asks for. Also, |n| <= 2^53 is far below the
            // numerator bound.
            lemma_pow2_mono(s as nat, 124nat);
            lemma_pow2_124();
            lemma_pow2_126();
            lemma_pow2_pos(s as nat);
            assert(n as int == parts_num(neg, mant, e));
            assert(d as int == parts_den(e));
            // `|n| <= 2^53 <= max_mag <= max_mag · d`, since `d >= 1`. The
            // proof runs on the literals. The mantissa bound is already a
            // literal, so there is no `pow2(53)` to pin.
            assert(abs_int(n as int) <= max_mag() * (d as int)) by (nonlinear_arith)
                requires
                    abs_int(n as int) <= 9007199254740992int,
                    max_mag() == pow2(62) - 1,
                    pow2(62) == 4611686018427387904int,
                    d as int >= 1,
            ;
            lemma_r2_r3_directed(n as int, d as int, dir);
        }
        Some(round_frac_exec(n, d, dir))
    } else {
        // |v| <= 2^53 · 2^-125 == 2^-72, strictly inside the first grid cell of
        // width 2^-61. `round_frac` therefore lands on that cell's endpoint.
        // `tiny` returns that endpoint, by `lemma_round_frac_subgrid`.
        proof {
            // `s` is ghost-only here. This branch computes nothing. It only
            // shows that `tiny` returns the value `round_frac` produces.
            let s = (-e) as nat;
            let n = parts_num(neg, mant, e);
            let d = parts_den(e);
            assert(d == pow2(s));
            lemma_pow2_pos(s);
            lemma_pow2_mono(125nat, s);
            lemma_pow2_125();
            // |n|·2^62 <= 2^53 · 2^62 == 2^115 < 2^125 <= d. The proof runs on
            // the literals rather than through a `pow2(53) + pow2(62)`
            // addition lemma. `2^53` is already a literal here, as the
            // mantissa bound in the precondition, and `2^62`/`2^125` are
            // pinned. Nothing remains to add.
            assert(abs_int(n) * pow2(62) <= 9007199254740992int
                * 4611686018427387904int) by (nonlinear_arith)
                requires
                    abs_int(n) <= 9007199254740992int,
                    pow2(62) == 4611686018427387904int,
            ;
            assert(abs_int(n) * pow2(62) < d) by (nonlinear_arith)
                requires
                    abs_int(n) * pow2(62) <= 9007199254740992int * 4611686018427387904int,
                    pow2(125) == 42535295865117307932921825928971026432int,
                    pow2(125) <= d,
            ;
            assert(abs_int(n) >= 1);
            assert(n != 0);
            assert((n > 0) == !neg);
            // `magnitude_fits`, and hence `!saturated`, comes back out of the
            // subgrid lemma. That lemma cannot reach `round_frac` without a
            // proof of `magnitude_fits` first. A re-derivation here duplicates
            // the same `nonlinear_arith` block in a second file.
            lemma_round_frac_subgrid(n, d, dir);
            lemma_r2_r3_directed(n, d, dir);
        }
        Some(tiny(neg, dir))
    }
}

/// The endpoint of the first dyadic cell, for a magnitude below `2^-62`.
/// Pinned to `round::subgrid_endpoint`, which `round::lemma_round_frac_subgrid`
/// identifies with `round_frac`.
pub fn tiny(neg: bool, dir: Dir) -> (r: Rat)
    ensures
        r.wf(),
        r == crate::round::subgrid_endpoint(!neg, dir),
{
    let eps_den: i64 = 2305843009213693952;  // 2^61
    proof {
        lemma_max_mag_pow2();
        lemma_pow2_61();
        lemma_pow2_62();
        // I1 for the two endpoints: `gcd(±1, 2^61)` is between 1 and 1.
        crate::gcd::lemma_gcd_pos(1nat, 2305843009213693952nat);
        crate::gcd::lemma_gcd_le(1nat, 2305843009213693952nat);
        assert(gcd_int(0, 1) == 1) by {
            reveal_with_fuel(gcd_nat, 3);
        }
        Rat::lemma_from_raw_spec_wf(0, 1);
        Rat::lemma_from_raw_spec_wf((-1int) as i64, eps_den);
        Rat::lemma_from_raw_spec_wf(1, eps_den);
    }
    match dir {
        Dir::Nearest => Rat::from_raw_parts(0, 1),
        Dir::Down => {
            if neg {
                Rat::from_raw_parts(-1, eps_den)
            } else {
                Rat::from_raw_parts(0, 1)
            }
        },
        Dir::Up => {
            if neg {
                Rat::from_raw_parts(0, 1)
            } else {
                Rat::from_raw_parts(1, eps_den)
            }
        },
    }
}

/// A `Rat` as an `f64`, for display only. TRUSTED. Three roundings, so about
/// `3·2^-53` relative; do not feed the result back into `Rat`.
#[verifier::external_body]
pub fn to_f64(q: Rat) -> f64 {
    (q.numerator() as f64) / (q.denominator() as f64)
}

// ---------------------------------------------------------------------------
// The decimal boundary (issue #33): `mantissa · 10^-scale`, exact where the
// budget allows it, rounded per `dir` otherwise. `rust_decimal::Decimal`
// guarantees `scale() <= MAX_DECIMAL_SCALE` and `|mantissa()| <=
// MAX_DECIMAL_MANTISSA`, exactly the domain accepted here, so the boundary in
// `convert.rs` below never observes `None` for a real `Decimal`.
// ---------------------------------------------------------------------------

/// `10^n` for `n <= MAX_DECIMAL_SCALE`, as a literal table (a loop needs an
/// invariant and an overflow lemma for the same result; `q::pow10_i64` is the
/// same idea one order of magnitude short of what a `Decimal` scale needs).
pub fn pow10_i128(n: u32) -> (r: i128)
    requires
        n <= MAX_DECIMAL_SCALE,
    ensures
        1 <= r <= 10000000000000000000000000000i128,
        r == pow10(n as nat),
{
    reveal_with_fuel(pow10, 30);
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
        18 => 1000000000000000000,
        19 => 10000000000000000000,
        20 => 100000000000000000000,
        21 => 1000000000000000000000,
        22 => 10000000000000000000000,
        23 => 100000000000000000000000,
        24 => 1000000000000000000000000,
        25 => 10000000000000000000000000,
        26 => 100000000000000000000000000,
        27 => 1000000000000000000000000000,
        _ => 10000000000000000000000000000,
    }
}

/// Convert the exact decimal `mantissa · 10^-scale` to a `Rat`, rounding in
/// direction `dir` when the value does not fit the width budget. `None` only
/// outside the domain a `rust_decimal::Decimal` can produce (`scale >
/// MAX_DECIMAL_SCALE`, or a mantissa wider than a 96-bit magnitude), so this
/// is total on every `Decimal`.
///
/// Unlike [`from_f64_dir`], there is no separate magnitude cutoff: a mantissa
/// whose exact value is beyond the crate's budget is not refused, it saturates
/// to the same `±MAX_MAG/1` boundary every other operation saturates to (R3,
/// scoped by `!saturated`; see `round.rs`). `crate::ext::Q`-level ingestion
/// (behind the `rust_decimal` feature) tests that condition separately and
/// reports it as `PosSat`/`NegSat`, matching `q_from_f64`.
pub fn from_decimal128_dir(mantissa: i128, scale: u32, dir: Dir) -> (r: Option<Rat>)
    ensures
        r.is_some() ==> r.unwrap().wf(),
        r.is_some() ==> r.unwrap() == round_frac(mantissa as int, pow10(scale as nat), dir),
        (r.is_some() && !crate::round::saturated(mantissa as int, pow10(scale as nat))) ==> {
            &&& dir == Dir::Down ==> q_le_frac(r.unwrap(), mantissa as int, pow10(scale as nat))
            &&& dir == Dir::Up ==> q_ge_frac(r.unwrap(), mantissa as int, pow10(scale as nat))
            &&& within_error_bound(r.unwrap(), mantissa as int, pow10(scale as nat))
        },
        r.is_none() <==> (scale > MAX_DECIMAL_SCALE || mantissa > MAX_DECIMAL_MANTISSA
            || mantissa < -MAX_DECIMAL_MANTISSA),
{
    if scale > MAX_DECIMAL_SCALE {
        return None;
    }
    if mantissa > MAX_DECIMAL_MANTISSA || mantissa < -MAX_DECIMAL_MANTISSA {
        return None;
    }
    let d: i128 = pow10_i128(scale);
    proof {
        lemma_pow2_124();
        lemma_pow2_126();
        assert(abs_int(mantissa as int) <= MAX_DECIMAL_MANTISSA as int);
        assert((MAX_DECIMAL_MANTISSA as int) < (pow2(126)));
        assert(d as int <= 10000000000000000000000000000int);
        assert(10000000000000000000000000000int <= pow2(124));
        if !crate::round::saturated(mantissa as int, d as int) {
            crate::round::lemma_r2_r3_directed(mantissa as int, d as int, dir);
        }
    }
    Some(round_frac_exec(mantissa, d, dir))
}

/// The exact decimal `mantissa · 10^-scale` as a `Rat`, `None` unless the
/// reduced `(mantissa, 10^scale)` pair already fits the width budget — the
/// domain [`from_decimal128_dir`] takes without rounding or saturating.
///
/// Wrapping the result in `crate::exact::Exact` then denotes the same value
/// as the decimal, not merely a `Rat` that happens not to need *further*
/// rounding: unlike `from_decimal128_dir`, this refuses exactly the cases
/// where the *ingestion itself* would have rounded, matching how `Exact`'s
/// own arithmetic reports rounding instead of performing it silently.
pub fn from_decimal128_exact(mantissa: i128, scale: u32) -> (r: Option<Rat>)
    ensures
        r.is_some() ==> r.unwrap().wf(),
        r.is_some() ==> q_is(r.unwrap(), mantissa as int, pow10(scale as nat)),
        r.is_none() <==> !(scale <= MAX_DECIMAL_SCALE && mantissa <= MAX_DECIMAL_MANTISSA
            && mantissa >= -MAX_DECIMAL_MANTISSA
            && crate::round::exact_path(mantissa as int, pow10(scale as nat))),
{
    if scale > MAX_DECIMAL_SCALE {
        return None;
    }
    if mantissa > MAX_DECIMAL_MANTISSA || mantissa < -MAX_DECIMAL_MANTISSA {
        return None;
    }
    let d: i128 = pow10_i128(scale);
    proof {
        lemma_pow2_124();
        lemma_pow2_126();
        assert(abs_int(mantissa as int) <= MAX_DECIMAL_MANTISSA as int);
        assert((MAX_DECIMAL_MANTISSA as int) < (pow2(126)));
        assert(d as int <= 10000000000000000000000000000int);
        assert(10000000000000000000000000000int <= pow2(124));
    }
    if crate::round::exact_path_exec(mantissa, d) {
        proof {
            crate::round::lemma_r1_identity(mantissa as int, d as int, Dir::Nearest);
        }
        Some(round_frac_exec(mantissa, d, Dir::Nearest))
    } else {
        None
    }
}

// ---------------------------------------------------------------------------
// The shared ratio core (issue #33 follow-up): every other library's exact
// fraction reduces to an `(n, d)` pair over `i128` and calls one of the two
// functions below. `from_decimal128_dir`/`from_decimal128_exact` above predate
// this and are left as they were verified (`d = 10^scale`, always positive,
// never needs the sign normalisation below); every *new* adapter in this
// module is built on this pair instead of repeating that proof shape.
// ---------------------------------------------------------------------------

/// `2^126 - 1`: the largest numerator magnitude [`from_ratio128_dir`] and
/// [`from_ratio128_exact`] accept. Chosen (rather than `i128::MAX`) so that
/// `abs(n) <= RATIO_N_LIMIT` implies the strict `abs(n) < num_input_bound()`
/// (`2^126`) `round_frac_exec` requires, and so that negating `n` below —
/// needed to fold a negative `d`'s sign onto it — never overflows.
pub const RATIO_N_LIMIT: i128 = 85070591730234615865843651857942052863;

/// `2^124`, exactly `den_input_bound()`: the largest denominator magnitude
/// the two functions below accept.
pub const RATIO_D_LIMIT: i128 = 21267647932558653966460912964485513216;

/// Convert the exact ratio `n / d` to a `Rat`, rounding in direction `dir`
/// once it no longer fits the width budget. `None` only when `d == 0`, or
/// either magnitude is too wide for `round_frac_exec` to accept at all
/// (`abs(n) <= 2^126 - 1`, `abs(d) <= 2^124`) — wider than that and no
/// `i128` pair can name the value in the first place, regardless of which
/// library produced it.
pub fn from_ratio128_dir(n: i128, d: i128, dir: Dir) -> (r: Option<Rat>)
    ensures
        r.is_some() ==> r.unwrap().wf(),
        r.is_some() ==> r.unwrap() == round_frac(
            crate::q::signed_den_num(n as int, d as int),
            abs_int(d as int),
            dir,
        ),
        (r.is_some() && !crate::round::saturated(
            crate::q::signed_den_num(n as int, d as int),
            abs_int(d as int),
        )) ==> {
            &&& dir == Dir::Down ==> q_le_frac(
                r.unwrap(),
                crate::q::signed_den_num(n as int, d as int),
                abs_int(d as int),
            )
            &&& dir == Dir::Up ==> q_ge_frac(
                r.unwrap(),
                crate::q::signed_den_num(n as int, d as int),
                abs_int(d as int),
            )
            &&& within_error_bound(
                r.unwrap(),
                crate::q::signed_den_num(n as int, d as int),
                abs_int(d as int),
            )
        },
        r.is_none() <==> (d == 0 || n > RATIO_N_LIMIT || n < -RATIO_N_LIMIT || d > RATIO_D_LIMIT
            || d < -RATIO_D_LIMIT),
{
    if d == 0 {
        return None;
    }
    if n > RATIO_N_LIMIT || n < -RATIO_N_LIMIT {
        return None;
    }
    if d > RATIO_D_LIMIT || d < -RATIO_D_LIMIT {
        return None;
    }
    let mut nn: i128 = n;
    let mut dd: i128 = d;
    if dd < 0 {
        nn = 0 - nn;
        dd = 0 - dd;
    }
    proof {
        lemma_pow2_124();
        lemma_pow2_126();
        if !crate::round::saturated(nn as int, dd as int) {
            crate::round::lemma_r2_r3_directed(nn as int, dd as int, dir);
        }
    }
    Some(round_frac_exec(nn, dd, dir))
}

/// The exact ratio `n / d` as a `Rat`, `None` unless the reduced pair already
/// fits the width budget — the domain [`from_ratio128_dir`] takes without
/// rounding or saturating. Wrapping the result in `crate::exact::Exact` then
/// denotes the same value as the original `n / d`, not merely a `Rat` that
/// happens not to need *further* rounding.
pub fn from_ratio128_exact(n: i128, d: i128) -> (r: Option<Rat>)
    ensures
        r.is_some() ==> r.unwrap().wf(),
        r.is_some() ==> q_is(
            r.unwrap(),
            crate::q::signed_den_num(n as int, d as int),
            abs_int(d as int),
        ),
        r.is_none() <==> !(d != 0 && n <= RATIO_N_LIMIT && n >= -RATIO_N_LIMIT
            && d <= RATIO_D_LIMIT && d >= -RATIO_D_LIMIT && crate::round::exact_path(
            crate::q::signed_den_num(n as int, d as int),
            abs_int(d as int),
        )),
{
    if d == 0 {
        return None;
    }
    if n > RATIO_N_LIMIT || n < -RATIO_N_LIMIT {
        return None;
    }
    if d > RATIO_D_LIMIT || d < -RATIO_D_LIMIT {
        return None;
    }
    let mut nn: i128 = n;
    let mut dd: i128 = d;
    if dd < 0 {
        nn = 0 - nn;
        dd = 0 - dd;
    }
    proof {
        lemma_pow2_124();
        lemma_pow2_126();
    }
    if crate::round::exact_path_exec(nn, dd) {
        proof {
            crate::round::lemma_r1_identity(nn as int, dd as int, Dir::Nearest);
        }
        Some(round_frac_exec(nn, dd, Dir::Nearest))
    } else {
        None
    }
}

} // verus!

// ---------------------------------------------------------------------------
// Display and serde. Outside the verified region, thin and total.
// ---------------------------------------------------------------------------

#[cfg_attr(verus_keep_ghost, verifier::external)]
impl core::fmt::Display for Rat {
    /// `"num/den"`, always in canonical form. The string is thus a faithful and
    /// unambiguous rendering of the value.
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}/{}", self.numerator(), self.denominator())
    }
}

/// The `(num, den)` pair, exact; decoding re-canonicalises through [`Rat::new`]
/// and rejects a malformed payload.
#[cfg(feature = "serde")]
#[cfg_attr(verus_keep_ghost, verifier::external)]
impl serde::Serialize for Rat {
    fn serialize<S: serde::Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        use serde::ser::SerializeTuple;
        let mut t = s.serialize_tuple(2)?;
        t.serialize_element(&self.numerator())?;
        t.serialize_element(&self.denominator())?;
        t.end()
    }
}

#[cfg(feature = "serde")]
#[cfg_attr(verus_keep_ghost, verifier::external)]
impl<'de> serde::Deserialize<'de> for Rat {
    fn deserialize<D: serde::Deserializer<'de>>(d: D) -> Result<Rat, D::Error> {
        use serde::de::Error;
        let (num, den) = <(i64, i64) as serde::Deserialize>::deserialize(d)?;
        Rat::new(num, den).ok_or_else(|| {
            D::Error::custom("the-q: (num, den) pair is not a representable rational")
        })
    }
}

// ---------------------------------------------------------------------------
// The extended `Q`: Display, FromStr and serde (issue #26 §8)
//
// All three share one spelling, rather than two spellings that can drift:
//
//     nan   inf   -inf   >max   <-max
//
// The saturation spellings are not readable as numbers. A numeral for `PosSat`
// is wrong in either direction. The value is finite, so `inf` is wrong. The
// value is also unknown, so `4611686018427387903` is worse: it claims an exact
// value that the type explicitly does not have.
// ---------------------------------------------------------------------------

/// The spelling of `Q::PosSat` in `Display`, `FromStr` and serde.
const POS_SAT_STR: &str = ">max";
/// The spelling of `Q::NegSat`.
const NEG_SAT_STR: &str = "<-max";
/// The spelling of `Q::PosInf`.
const POS_INF_STR: &str = "inf";
/// The spelling of `Q::NegInf`.
const NEG_INF_STR: &str = "-inf";
/// The spelling of `Q::Nan`.
const NAN_STR: &str = "nan";

#[cfg_attr(verus_keep_ghost, verifier::external)]
impl core::fmt::Display for crate::ext::Q {
    /// `"num/den"` for a number, and the fixed spelling above for each special.
    ///
    /// Every output round-trips through [`FromStr`](core::str::FromStr).
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            crate::ext::Q::Number(x) => write!(f, "{}", x),
            crate::ext::Q::PosSat => f.write_str(POS_SAT_STR),
            crate::ext::Q::NegSat => f.write_str(NEG_SAT_STR),
            crate::ext::Q::PosInf => f.write_str(POS_INF_STR),
            crate::ext::Q::NegInf => f.write_str(NEG_INF_STR),
            crate::ext::Q::Nan => f.write_str(NAN_STR),
        }
    }
}

/// Why a string could not be parsed as a [`Q`](crate::ext::Q).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum ParseQError {
    /// The input matched no special spelling and was not of the form
    /// `int` or `int/int`.
    Malformed,
    /// A numeral did not fit an `i64`.
    IntOverflow,
    /// The denominator was zero. `"1/0"` in input is a malformed numeral, not a
    /// computation, so it is rejected rather than read as `PosInf`.
    ZeroDenominator,
    /// The pair does not reduce to a value inside the width budget.
    OutOfBudget,
}

#[cfg_attr(verus_keep_ghost, verifier::external)]
impl core::fmt::Display for ParseQError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(match self {
            ParseQError::Malformed => "the-q: not a rational or a recognised special",
            ParseQError::IntOverflow => "the-q: numeral does not fit an i64",
            ParseQError::ZeroDenominator => "the-q: denominator is zero",
            ParseQError::OutOfBudget => "the-q: value is outside the width budget",
        })
    }
}

impl std::error::Error for ParseQError {}

#[cfg_attr(verus_keep_ghost, verifier::external)]
impl core::str::FromStr for crate::ext::Q {
    type Err = ParseQError;

    /// Parses what [`Display`](core::fmt::Display) produces, plus a bare integer.
    /// Specials are case-insensitive; surrounding whitespace is rejected.
    fn from_str(s: &str) -> Result<Self, ParseQError> {
        use crate::ext::Q;

        if s.eq_ignore_ascii_case(NAN_STR) {
            return Ok(Q::Nan);
        }
        if s.eq_ignore_ascii_case(POS_INF_STR) {
            return Ok(Q::PosInf);
        }
        if s.eq_ignore_ascii_case(NEG_INF_STR) {
            return Ok(Q::NegInf);
        }
        // The saturation spellings contain no letters, so the case-insensitive
        // comparison is only for uniformity of treatment.
        if s.eq_ignore_ascii_case(POS_SAT_STR) {
            return Ok(Q::PosSat);
        }
        if s.eq_ignore_ascii_case(NEG_SAT_STR) {
            return Ok(Q::NegSat);
        }

        let (num_str, den_str) = match s.split_once('/') {
            Some((n, d)) => (n, d),
            None => (s, "1"),
        };
        // `split_once` on `"//"` yields `("", "/")`, and on `"1/2/3"` yields
        // `("1", "2/3")`. Both inputs fail here, which is the intent.
        let num: i64 = parse_i64(num_str)?;
        let den: i64 = parse_i64(den_str)?;
        if den == 0 {
            return Err(ParseQError::ZeroDenominator);
        }
        match crate::types::Rat::new(num, den) {
            Some(x) => Ok(Q::Number(x)),
            None => Err(ParseQError::OutOfBudget),
        }
    }
}

/// `i64::from_str`, distinguishing overflow from a malformed numeral by a
/// syntactic check rather than a wider re-parse.
#[cfg_attr(verus_keep_ghost, verifier::external)]
fn parse_i64(s: &str) -> Result<i64, ParseQError> {
    match s.parse::<i64>() {
        Ok(v) => Ok(v),
        Err(_) => {
            let digits = s.strip_prefix(['+', '-']).unwrap_or(s);
            if !digits.is_empty() && digits.bytes().all(|b| b.is_ascii_digit()) {
                Err(ParseQError::IntOverflow)
            } else {
                Err(ParseQError::Malformed)
            }
        }
    }
}

/// A number as the `(num, den)` pair, a special as its string. Untagged, so
/// it decodes only in self-describing formats; `bincode` fails at run time.
#[cfg(feature = "serde")]
#[cfg_attr(verus_keep_ghost, verifier::external)]
impl serde::Serialize for crate::ext::Q {
    fn serialize<S: serde::Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        match self {
            crate::ext::Q::Number(x) => x.serialize(s),
            crate::ext::Q::PosSat => s.serialize_str(POS_SAT_STR),
            crate::ext::Q::NegSat => s.serialize_str(NEG_SAT_STR),
            crate::ext::Q::PosInf => s.serialize_str(POS_INF_STR),
            crate::ext::Q::NegInf => s.serialize_str(NEG_INF_STR),
            crate::ext::Q::Nan => s.serialize_str(NAN_STR),
        }
    }
}

#[cfg(feature = "serde")]
#[cfg_attr(verus_keep_ghost, verifier::external)]
impl<'de> serde::Deserialize<'de> for crate::ext::Q {
    fn deserialize<D: serde::Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        struct V;

        impl<'de> serde::de::Visitor<'de> for V {
            type Value = crate::ext::Q;

            fn expecting(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                f.write_str(
                    "a [num, den] pair or one of \"nan\", \"inf\", \"-inf\", \">max\", \"<-max\"",
                )
            }

            fn visit_str<E: serde::de::Error>(self, v: &str) -> Result<Self::Value, E> {
                use crate::ext::Q;
                // Exact match, not the case-insensitive `FromStr` spelling. A
                // wire format is machine-written. A case variant therefore
                // means an encoder disagrees with this one. The mismatch is
                // caught rather than absorbed.
                match v {
                    NAN_STR => Ok(Q::Nan),
                    POS_INF_STR => Ok(Q::PosInf),
                    NEG_INF_STR => Ok(Q::NegInf),
                    POS_SAT_STR => Ok(Q::PosSat),
                    NEG_SAT_STR => Ok(Q::NegSat),
                    _ => Err(E::custom("the-q: unrecognised special-value string")),
                }
            }

            fn visit_seq<A: serde::de::SeqAccess<'de>>(
                self,
                mut seq: A,
            ) -> Result<Self::Value, A::Error> {
                use serde::de::Error;
                let num: i64 = seq
                    .next_element()?
                    .ok_or_else(|| A::Error::custom("the-q: missing numerator"))?;
                let den: i64 = seq
                    .next_element()?
                    .ok_or_else(|| A::Error::custom("the-q: missing denominator"))?;
                if seq.next_element::<serde::de::IgnoredAny>()?.is_some() {
                    return Err(A::Error::custom("the-q: expected exactly two elements"));
                }
                // Through `Rat::new`, so `[2, 4]` decodes as `1/2` and an unrepresentable
                // pair is an error, not a saturation.
                crate::types::Rat::new(num, den)
                    .map(crate::ext::Q::Number)
                    .ok_or_else(|| {
                        A::Error::custom("the-q: (num, den) pair is not a representable rational")
                    })
            }
        }

        // `deserialize_any` is what confines this to self-describing formats.
        d.deserialize_any(V)
    }
}

// ---------------------------------------------------------------------------
// The f64 boundary for the extended type (issue #26 §8)
// ---------------------------------------------------------------------------

/// An `f64` as a `Q`, total: NaN → `Nan`, `±inf` → `±Inf`, an over-budget
/// finite value saturates by sign. There is deliberately no `Q → f64`: no
/// float honestly denotes `PosSat`. Outside the verified region because it
/// uses `is_nan`/`is_infinite`/`is_sign_negative`; the value path is
/// [`from_f64_dir`].
#[cfg_attr(verus_keep_ghost, verifier::external)]
pub fn q_from_f64(v: f64) -> crate::ext::Q {
    use crate::ext::Q;
    if v.is_nan() {
        return Q::Nan;
    }
    if v.is_infinite() {
        return if v.is_sign_negative() {
            Q::NegInf
        } else {
            Q::PosInf
        };
    }
    match from_f64_dir(v, crate::types::Dir::Nearest) {
        Some(x) => Q::Number(x),
        // Finite but outside the budget: saturate by sign rather than fail.
        // `v` is finite and non-representable, so it is genuinely large.
        None => {
            if v.is_sign_negative() {
                Q::NegSat
            } else {
                Q::PosSat
            }
        }
    }
}

// ---------------------------------------------------------------------------
// The `rust_decimal` boundary (issue #33)
//
// `rust_decimal::Decimal` stores `mantissa · 10^-scale` exactly, with no
// rounding of its own (`scale() <= 28`, `|mantissa()| <= 2^96 - 1`). That
// domain is exactly what `from_decimal128_dir` accepts, so the conversion
// below is total on every `Decimal` and never takes the defensive `None`
// branch that function keeps for a malformed `(mantissa, scale)` pair.
// ---------------------------------------------------------------------------

/// `rust_decimal::Decimal` as a `Rat`, rounding in direction `dir` when the
/// exact value does not fit the width budget (it then saturates to
/// `±MAX_MAG/1`, per R3). Exact whenever the reduced value fits, regardless of
/// `dir` — the crate's `mantissa()`/`scale()` pair is fed straight to
/// [`from_decimal128_dir`], the verified core.
#[cfg(feature = "rust_decimal")]
#[cfg_attr(verus_keep_ghost, verifier::external)]
pub fn from_rust_decimal_dir(v: rust_decimal::Decimal, dir: Dir) -> Rat {
    match from_decimal128_dir(v.mantissa(), v.scale(), dir) {
        Some(x) => x,
        // Unreachable for a genuine `Decimal`: `scale() <= MAX_DECIMAL_SCALE`
        // and `|mantissa()| <= MAX_DECIMAL_MANTISSA` are its own invariants.
        None => unreachable!(
            "the-q: rust_decimal::Decimal violated its own (mantissa, scale) invariant"
        ),
    }
}

/// `rust_decimal::Decimal` as a `Q`, rounding to nearest. Saturates by sign
/// once the magnitude leaves the budget, mirroring [`q_from_f64`], rather than
/// silently returning the clamped boundary `Rat` that [`from_rust_decimal_dir`]
/// would.
#[cfg(feature = "rust_decimal")]
#[cfg_attr(verus_keep_ghost, verifier::external)]
pub fn q_from_rust_decimal(v: rust_decimal::Decimal) -> crate::ext::Q {
    use crate::ext::Q;
    let mantissa = v.mantissa();
    let scale = v.scale();
    let d = pow10_i128(scale);
    if crate::q::magnitude_fits_exec(mantissa, d) {
        Q::Number(from_rust_decimal_dir(v, crate::types::Dir::Nearest))
    } else if mantissa > 0 {
        Q::PosSat
    } else {
        Q::NegSat
    }
}

#[cfg(feature = "rust_decimal")]
#[cfg_attr(verus_keep_ghost, verifier::external)]
impl From<rust_decimal::Decimal> for crate::ext::Q {
    /// Rounds to nearest; see [`q_from_rust_decimal`].
    fn from(v: rust_decimal::Decimal) -> Self {
        q_from_rust_decimal(v)
    }
}

/// `rust_decimal::Decimal` as an [`Exact`](crate::exact::Exact) —
/// `Err(ExactError::Inexact)` when the reduced `(mantissa, 10^scale)` pair
/// does not already fit the width budget, rather than silently handing back
/// an `Exact` that has already rounded on the way in. `Exact`'s own
/// `add`/`sub`/`mul`/`div` report rounding the same way; this makes ingestion
/// consistent with them, instead of a `Rat` conversion (which does round or
/// saturate) wrapped in `Exact::new` after the fact.
#[cfg(feature = "rust_decimal")]
#[cfg_attr(verus_keep_ghost, verifier::external)]
pub fn exact_from_rust_decimal(
    v: rust_decimal::Decimal,
) -> Result<crate::exact::Exact, crate::exact::ExactError> {
    match from_decimal128_exact(v.mantissa(), v.scale()) {
        Some(x) => Ok(crate::exact::Exact::new(x)),
        None => Err(crate::exact::ExactError::Inexact),
    }
}

#[cfg(feature = "rust_decimal")]
#[cfg_attr(verus_keep_ghost, verifier::external)]
impl TryFrom<rust_decimal::Decimal> for crate::exact::Exact {
    type Error = crate::exact::ExactError;

    /// See [`exact_from_rust_decimal`].
    fn try_from(v: rust_decimal::Decimal) -> Result<Self, Self::Error> {
        exact_from_rust_decimal(v)
    }
}

// ---------------------------------------------------------------------------
// Shared tails for every external-library `Q`/`Exact` adapter below. Each
// adapter reduces its own representation to an `(n, d)` pair (`d > 0`) and
// calls one of these two, the same way each `Rat` adapter calls
// `from_ratio128_dir`/`from_ratio128_exact`.
// ---------------------------------------------------------------------------

/// `n / d` (`d > 0`) as a `Q`, rounding to nearest and saturating by sign
/// once the magnitude alone leaves the budget — mirroring [`q_from_f64`].
#[cfg(any(
    feature = "fixed",
    feature = "num-rational",
    feature = "num-bigint",
    feature = "bigdecimal"
))]
#[cfg_attr(verus_keep_ghost, verifier::external)]
fn q_from_ratio128(n: i128, d: i128) -> crate::ext::Q {
    use crate::ext::Q;
    if n > RATIO_N_LIMIT || n < -RATIO_N_LIMIT {
        return if n < 0 { Q::NegSat } else { Q::PosSat };
    }
    if crate::q::magnitude_fits_exec(n, d) {
        Q::Number(
            from_ratio128_dir(n, d, crate::types::Dir::Nearest)
                .expect("the-q: n and d were just bound-checked above"),
        )
    } else if n > 0 {
        Q::PosSat
    } else {
        Q::NegSat
    }
}

/// `n / d` as an [`Exact`](crate::exact::Exact), `Err(ExactError::Inexact)`
/// unless the reduced pair already fits the width budget.
#[cfg(any(
    feature = "fixed",
    feature = "num-rational",
    feature = "num-bigint",
    feature = "bigdecimal"
))]
#[cfg_attr(verus_keep_ghost, verifier::external)]
fn exact_from_ratio128(n: i128, d: i128) -> Result<crate::exact::Exact, crate::exact::ExactError> {
    match from_ratio128_exact(n, d) {
        Some(x) => Ok(crate::exact::Exact::new(x)),
        None => Err(crate::exact::ExactError::Inexact),
    }
}

// ---------------------------------------------------------------------------
// The `fixed` boundary: any 128-bit-backed fixed-point type as `Rat`/`Q`/
// `Exact`. `fixed::types::I*F*` aliases whose bits total 128 (`I0F128` through
// `I127F1`, e.g. `I64F64`) all share `Bits = i128`, so one generic function
// covers the whole family: the value is `bits · 2^-FRAC_NBITS`, exactly the
// dyadic sibling of the decimal boundary's `mantissa · 10^-scale`.
// ---------------------------------------------------------------------------

/// Any 128-bit-backed `fixed` type as a `Rat`, rounding in direction `dir`
/// once `bits / 2^FRAC_NBITS` no longer fits the width budget. `FRAC_NBITS >
/// 126` refuses outright: `2^127` and up does not fit an `i128` denominator
/// at all, so no `(n, d)` pair can name the value here in the first place —
/// this is a limit of representing the value as an exact `i128` ratio, not a
/// further approximation on top of one.
#[cfg(feature = "fixed")]
#[cfg_attr(verus_keep_ghost, verifier::external)]
pub fn from_fixed_dir<F>(v: F, dir: Dir) -> Option<Rat>
where
    F: fixed::traits::Fixed<Bits = i128>,
{
    if F::FRAC_NBITS > 126 {
        return None;
    }
    let d = crate::round::pow2_i128(F::FRAC_NBITS);
    from_ratio128_dir(v.to_bits(), d, dir)
}

/// The exact value of a 128-bit-backed `fixed` type as a `Rat`, `None` unless
/// the reduced `(bits, 2^FRAC_NBITS)` pair already fits the width budget.
#[cfg(feature = "fixed")]
#[cfg_attr(verus_keep_ghost, verifier::external)]
pub fn from_fixed_exact<F>(v: F) -> Option<Rat>
where
    F: fixed::traits::Fixed<Bits = i128>,
{
    if F::FRAC_NBITS > 126 {
        return None;
    }
    let d = crate::round::pow2_i128(F::FRAC_NBITS);
    from_ratio128_exact(v.to_bits(), d)
}

/// Any 128-bit-backed `fixed` type as a `Q`, rounding to nearest and
/// saturating by sign past the budget. Past `FRAC_NBITS > 126` (where no
/// `i128` denominator can name the value, per [`from_fixed_dir`]) this falls
/// back to a lossy `to_num::<f64>()` conversion through [`q_from_f64`] rather
/// than guessing a saturation sign: that domain is `INT_NBITS < 2`, values
/// bounded near `[-1, 1)`, nowhere near the budget's ceiling, so a magnitude
/// this function cannot represent exactly is never actually saturated.
///
/// A named function, not `impl From<F> for Q`: a blanket `impl<F: Fixed<..>>
/// From<F> for Q` cannot coexist with the concrete `impl From<Decimal> for Q`
/// above (or any future concrete one) — the compiler cannot rule out some
/// downstream type implementing both `Fixed` and, say, being `Decimal`
/// itself, so it refuses the overlap outright (`E0119`). The same reasoning
/// rules out a blanket `TryFrom<F> for Exact` below.
#[cfg(feature = "fixed")]
#[cfg_attr(verus_keep_ghost, verifier::external)]
pub fn q_from_fixed<F>(v: F) -> crate::ext::Q
where
    F: fixed::traits::Fixed<Bits = i128>,
{
    if F::FRAC_NBITS > 126 {
        return q_from_f64(v.to_num::<f64>());
    }
    let d = crate::round::pow2_i128(F::FRAC_NBITS);
    q_from_ratio128(v.to_bits(), d)
}

/// Any 128-bit-backed `fixed` type as an [`Exact`](crate::exact::Exact) —
/// `Err(ExactError::Inexact)` when the reduced pair does not already fit the
/// width budget, `FRAC_NBITS > 126` included.
#[cfg(feature = "fixed")]
#[cfg_attr(verus_keep_ghost, verifier::external)]
pub fn exact_from_fixed<F>(v: F) -> Result<crate::exact::Exact, crate::exact::ExactError>
where
    F: fixed::traits::Fixed<Bits = i128>,
{
    if F::FRAC_NBITS > 126 {
        return Err(crate::exact::ExactError::Inexact);
    }
    let d = crate::round::pow2_i128(F::FRAC_NBITS);
    exact_from_ratio128(v.to_bits(), d)
}

// ---------------------------------------------------------------------------
// The `num-rational` boundary: `Ratio<i64>` (always exact, no truncation
// needed) and `BigRational` (arbitrary precision; needs a fallible `i128`
// extraction first).
// ---------------------------------------------------------------------------

/// `num_rational::Ratio<i64>` as a `Rat`, rounding in direction `dir` once it
/// leaves the width budget. `Ratio`'s own invariant (a nonzero denominator)
/// is exactly what `from_ratio128_dir` needs to never return `None` on an
/// `i64` pair, so this is total.
#[cfg(feature = "num-rational")]
#[cfg_attr(verus_keep_ghost, verifier::external)]
pub fn from_num_rational_i64_dir(v: num_rational::Ratio<i64>, dir: Dir) -> Rat {
    from_ratio128_dir(i128::from(*v.numer()), i128::from(*v.denom()), dir)
        .expect("the-q: an i64 pair is always within from_ratio128_dir's domain")
}

/// The exact value of a `num_rational::Ratio<i64>` as a `Rat`, `None` unless
/// the reduced pair already fits the width budget.
#[cfg(feature = "num-rational")]
#[cfg_attr(verus_keep_ghost, verifier::external)]
pub fn from_num_rational_i64_exact(v: num_rational::Ratio<i64>) -> Option<Rat> {
    from_ratio128_exact(i128::from(*v.numer()), i128::from(*v.denom()))
}

/// `num_rational::Ratio<i64>` as a `Q`, rounding to nearest and saturating by
/// sign past the budget.
#[cfg(feature = "num-rational")]
#[cfg_attr(verus_keep_ghost, verifier::external)]
pub fn q_from_num_rational_i64(v: num_rational::Ratio<i64>) -> crate::ext::Q {
    q_from_ratio128(i128::from(*v.numer()), i128::from(*v.denom()))
}

#[cfg(feature = "num-rational")]
#[cfg_attr(verus_keep_ghost, verifier::external)]
impl From<num_rational::Ratio<i64>> for crate::ext::Q {
    /// Rounds to nearest; see [`q_from_num_rational_i64`].
    fn from(v: num_rational::Ratio<i64>) -> Self {
        q_from_num_rational_i64(v)
    }
}

/// `num_rational::Ratio<i64>` as an [`Exact`](crate::exact::Exact) —
/// `Err(ExactError::Inexact)` unless the reduced pair already fits the width
/// budget.
#[cfg(feature = "num-rational")]
#[cfg_attr(verus_keep_ghost, verifier::external)]
pub fn exact_from_num_rational_i64(
    v: num_rational::Ratio<i64>,
) -> Result<crate::exact::Exact, crate::exact::ExactError> {
    exact_from_ratio128(i128::from(*v.numer()), i128::from(*v.denom()))
}

#[cfg(feature = "num-rational")]
#[cfg_attr(verus_keep_ghost, verifier::external)]
impl TryFrom<num_rational::Ratio<i64>> for crate::exact::Exact {
    type Error = crate::exact::ExactError;

    /// See [`exact_from_num_rational_i64`].
    fn try_from(v: num_rational::Ratio<i64>) -> Result<Self, Self::Error> {
        exact_from_num_rational_i64(v)
    }
}

/// `num_rational::BigRational` as a `Rat`, rounding in direction `dir`.
/// `None` when either the (already-reduced, by `Ratio`'s own invariant)
/// numerator or denominator does not fit an `i128` — arbitrary precision
/// means there is always a `BigRational` outside any fixed-width
/// representation.
#[cfg(feature = "num-rational")]
#[cfg_attr(verus_keep_ghost, verifier::external)]
pub fn from_big_rational_dir(v: &num_rational::BigRational, dir: Dir) -> Option<Rat> {
    let n = i128::try_from(v.numer()).ok()?;
    let d = i128::try_from(v.denom()).ok()?;
    from_ratio128_dir(n, d, dir)
}

/// The exact value of a `BigRational` as a `Rat`, `None` unless both the
/// reduced numerator and denominator fit an `i128` and that pair already
/// fits the width budget.
#[cfg(feature = "num-rational")]
#[cfg_attr(verus_keep_ghost, verifier::external)]
pub fn from_big_rational_exact(v: &num_rational::BigRational) -> Option<Rat> {
    let n = i128::try_from(v.numer()).ok()?;
    let d = i128::try_from(v.denom()).ok()?;
    from_ratio128_exact(n, d)
}

/// `BigRational` as a `Q`, rounding to nearest. When the reduced numerator
/// and denominator both fit an `i128`, this saturates by sign past the
/// budget like every other adapter here; short of that it falls back to a
/// lossy `to_f64` conversion (through [`q_from_f64`]) rather than guessing a
/// saturation sign, because `Ratio` reduces its terms to lowest form and
/// nothing bounds *those* by the value's own magnitude — `(10^100 + 1) /
/// 10^100` is a value near `1`, not one anywhere near the budget's ceiling,
/// even though neither term fits `i128`.
#[cfg(feature = "num-rational")]
#[cfg_attr(verus_keep_ghost, verifier::external)]
pub fn q_from_big_rational(v: &num_rational::BigRational) -> crate::ext::Q {
    match (i128::try_from(v.numer()), i128::try_from(v.denom())) {
        (Ok(n), Ok(d)) => q_from_ratio128(n, d),
        _ => q_from_f64(num_traits::ToPrimitive::to_f64(v).unwrap_or(f64::NAN)),
    }
}

#[cfg(feature = "num-rational")]
#[cfg_attr(verus_keep_ghost, verifier::external)]
impl From<num_rational::BigRational> for crate::ext::Q {
    /// Rounds to nearest; see [`q_from_big_rational`].
    fn from(v: num_rational::BigRational) -> Self {
        q_from_big_rational(&v)
    }
}

/// `BigRational` as an [`Exact`](crate::exact::Exact) —
/// `Err(ExactError::Inexact)` unless both the reduced numerator and
/// denominator fit an `i128` and that pair already fits the width budget.
#[cfg(feature = "num-rational")]
#[cfg_attr(verus_keep_ghost, verifier::external)]
pub fn exact_from_big_rational(
    v: &num_rational::BigRational,
) -> Result<crate::exact::Exact, crate::exact::ExactError> {
    let n = i128::try_from(v.numer()).map_err(|_| crate::exact::ExactError::Inexact)?;
    let d = i128::try_from(v.denom()).map_err(|_| crate::exact::ExactError::Inexact)?;
    exact_from_ratio128(n, d)
}

#[cfg(feature = "num-rational")]
#[cfg_attr(verus_keep_ghost, verifier::external)]
impl TryFrom<num_rational::BigRational> for crate::exact::Exact {
    type Error = crate::exact::ExactError;

    /// See [`exact_from_big_rational`].
    fn try_from(v: num_rational::BigRational) -> Result<Self, Self::Error> {
        exact_from_big_rational(&v)
    }
}

// ---------------------------------------------------------------------------
// The `num-bigint` boundary: a bare `BigInt`, i.e. `n / 1`. Unlike
// `BigRational`, an integer's own magnitude *is* the value — there is no
// reduced-terms ambiguity — so "does not fit `i128`" always means "the
// magnitude itself is too wide", and saturation by sign is exact, not a
// fallback.
// ---------------------------------------------------------------------------

/// `num_bigint::BigInt` as a `Rat`, rounding in direction `dir`. `None` when
/// the integer itself does not fit an `i128`.
#[cfg(feature = "num-bigint")]
#[cfg_attr(verus_keep_ghost, verifier::external)]
pub fn from_bigint_dir(v: &num_bigint::BigInt, dir: Dir) -> Option<Rat> {
    let n = i128::try_from(v).ok()?;
    from_ratio128_dir(n, 1, dir)
}

/// The exact value of a `BigInt` as a `Rat`, `None` unless it fits an `i128`
/// and is within `MAX_MAG`.
#[cfg(feature = "num-bigint")]
#[cfg_attr(verus_keep_ghost, verifier::external)]
pub fn from_bigint_exact(v: &num_bigint::BigInt) -> Option<Rat> {
    let n = i128::try_from(v).ok()?;
    from_ratio128_exact(n, 1)
}

/// `BigInt` as a `Q`, saturating by sign once the integer itself no longer
/// fits an `i128` (equivalently, once it exceeds `MAX_MAG`, since past that
/// this is still exactly the "too big" case, not a resolution limit).
#[cfg(feature = "num-bigint")]
#[cfg_attr(verus_keep_ghost, verifier::external)]
pub fn q_from_bigint(v: &num_bigint::BigInt) -> crate::ext::Q {
    use crate::ext::Q;
    match i128::try_from(v) {
        Ok(n) => q_from_ratio128(n, 1),
        Err(_) => {
            if v.sign() == num_bigint::Sign::Minus {
                Q::NegSat
            } else {
                Q::PosSat
            }
        }
    }
}

#[cfg(feature = "num-bigint")]
#[cfg_attr(verus_keep_ghost, verifier::external)]
impl From<num_bigint::BigInt> for crate::ext::Q {
    /// See [`q_from_bigint`].
    fn from(v: num_bigint::BigInt) -> Self {
        q_from_bigint(&v)
    }
}

/// `BigInt` as an [`Exact`](crate::exact::Exact) — `Err(ExactError::Inexact)`
/// unless it fits an `i128` and is within `MAX_MAG`.
#[cfg(feature = "num-bigint")]
#[cfg_attr(verus_keep_ghost, verifier::external)]
pub fn exact_from_bigint(
    v: &num_bigint::BigInt,
) -> Result<crate::exact::Exact, crate::exact::ExactError> {
    let n = i128::try_from(v).map_err(|_| crate::exact::ExactError::Inexact)?;
    exact_from_ratio128(n, 1)
}

#[cfg(feature = "num-bigint")]
#[cfg_attr(verus_keep_ghost, verifier::external)]
impl TryFrom<num_bigint::BigInt> for crate::exact::Exact {
    type Error = crate::exact::ExactError;

    /// See [`exact_from_bigint`].
    fn try_from(v: num_bigint::BigInt) -> Result<Self, Self::Error> {
        exact_from_bigint(&v)
    }
}

// ---------------------------------------------------------------------------
// The `bigdecimal` boundary: `BigDecimal` is `digits · 10^-scale` with an
// arbitrary-precision `digits` and an `i64` `scale` that (unlike
// `rust_decimal::Decimal`'s) may be negative, meaning `digits · 10^|scale|`.
// Negative-scale values are normalised to that product (still exact, still
// arbitrary precision) before the same fallible `i128` extraction the other
// big-number boundaries use.
// ---------------------------------------------------------------------------

/// `(n, 10^scale)` for a `BigDecimal`, both as `i128`, when representable at
/// all: `None` when the (possibly negative-scale-normalised) digits do not
/// fit an `i128`, or the resulting scale exceeds [`MAX_DECIMAL_SCALE`]. A
/// negative scale beyond -40 is refused before doing any arbitrary-precision
/// multiplication for it, since `digits · 10^40` is already far past any
/// `i128`.
#[cfg(feature = "bigdecimal")]
#[cfg_attr(verus_keep_ghost, verifier::external)]
fn bigdecimal_ratio_i128(v: &bigdecimal::BigDecimal) -> Option<(i128, i128)> {
    let (digits, scale) = v.as_bigint_and_scale();
    if scale >= 0 {
        if scale > i64::from(MAX_DECIMAL_SCALE) {
            return None;
        }
        let n = i128::try_from(digits.as_ref()).ok()?;
        let d = pow10_i128(u32::try_from(scale).ok()?);
        Some((n, d))
    } else {
        let shift = scale.checked_neg()?;
        if shift > 40 {
            return None;
        }
        let factor = num_bigint::BigInt::from(10u8).pow(u32::try_from(shift).ok()?);
        let n_big = digits.into_owned() * factor;
        let n = i128::try_from(&n_big).ok()?;
        Some((n, 1))
    }
}

/// `bigdecimal::BigDecimal` as a `Rat`, rounding in direction `dir`. `None`
/// outside [`bigdecimal_ratio_i128`]'s domain.
#[cfg(feature = "bigdecimal")]
#[cfg_attr(verus_keep_ghost, verifier::external)]
pub fn from_bigdecimal_dir(v: &bigdecimal::BigDecimal, dir: Dir) -> Option<Rat> {
    let (n, d) = bigdecimal_ratio_i128(v)?;
    from_ratio128_dir(n, d, dir)
}

/// The exact value of a `BigDecimal` as a `Rat`, `None` unless it is inside
/// [`bigdecimal_ratio_i128`]'s domain and that pair already fits the width
/// budget.
#[cfg(feature = "bigdecimal")]
#[cfg_attr(verus_keep_ghost, verifier::external)]
pub fn from_bigdecimal_exact(v: &bigdecimal::BigDecimal) -> Option<Rat> {
    let (n, d) = bigdecimal_ratio_i128(v)?;
    from_ratio128_exact(n, d)
}

/// `BigDecimal` as a `Q`, rounding to nearest. Falls back to a lossy `to_f64`
/// conversion (through [`q_from_f64`]) outside [`bigdecimal_ratio_i128`]'s
/// domain, the same way [`q_from_big_rational`] does and for the same
/// reason: arbitrarily many digits do not imply an arbitrarily large value.
#[cfg(feature = "bigdecimal")]
#[cfg_attr(verus_keep_ghost, verifier::external)]
pub fn q_from_bigdecimal(v: &bigdecimal::BigDecimal) -> crate::ext::Q {
    match bigdecimal_ratio_i128(v) {
        Some((n, d)) => q_from_ratio128(n, d),
        None => q_from_f64(num_traits::ToPrimitive::to_f64(v).unwrap_or(f64::NAN)),
    }
}

#[cfg(feature = "bigdecimal")]
#[cfg_attr(verus_keep_ghost, verifier::external)]
impl From<bigdecimal::BigDecimal> for crate::ext::Q {
    /// Rounds to nearest; see [`q_from_bigdecimal`].
    fn from(v: bigdecimal::BigDecimal) -> Self {
        q_from_bigdecimal(&v)
    }
}

/// `BigDecimal` as an [`Exact`](crate::exact::Exact) —
/// `Err(ExactError::Inexact)` outside [`bigdecimal_ratio_i128`]'s domain or
/// when that pair does not already fit the width budget.
#[cfg(feature = "bigdecimal")]
#[cfg_attr(verus_keep_ghost, verifier::external)]
pub fn exact_from_bigdecimal(
    v: &bigdecimal::BigDecimal,
) -> Result<crate::exact::Exact, crate::exact::ExactError> {
    let (n, d) = bigdecimal_ratio_i128(v).ok_or(crate::exact::ExactError::Inexact)?;
    exact_from_ratio128(n, d)
}

#[cfg(feature = "bigdecimal")]
#[cfg_attr(verus_keep_ghost, verifier::external)]
impl TryFrom<bigdecimal::BigDecimal> for crate::exact::Exact {
    type Error = crate::exact::ExactError;

    /// See [`exact_from_bigdecimal`].
    fn try_from(v: bigdecimal::BigDecimal) -> Result<Self, Self::Error> {
        exact_from_bigdecimal(&v)
    }
}
