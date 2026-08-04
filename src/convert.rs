//! The crate's edges: `f64` in, `f64` out, `Display`, `serde`.
//!
//! # The trusted boundary
//!
//! Exactly two functions in this crate touch a float, and both are at the edge:
//!
//! * [`f64_decompose`] — pulls the IEEE-754 binary64 fields out of a `f64`.
//!   `external_body`, because Verus has no model of `f64::to_bits`. Everything
//!   downstream of it — turning `(sign, mantissa, exponent)` into a rational and
//!   rounding it — is ordinary verified integer arithmetic. The *only* thing
//!   assumed is that the triple denotes the float.
//! * [`to_f64`] — display/DTO only. `external_body`. Never feed its output back
//!   into `Rat` arithmetic; that would silently reintroduce every `f64` problem
//!   this crate exists to remove.
//!
//! Both are enumerated in `TRUSTED.md` with their assumed specifications and
//! the differential tests that back them.
//!
//! # Why the input path is exact
//!
//! An `f64` *is* a rational: `±m · 2^e` with a 53-bit `m`. So `from_f64_dir`
//! does no floating-point reasoning at all — it builds `m / 2^-e` (or `m · 2^e`
//! over `1`) as integers and hands the pair to the same verified rounding
//! function every arithmetic operation uses.

use verus_builtin_macros::verus;

#[allow(unused_imports)]
use verus_builtin::*;
#[allow(unused_imports)]
use vstd::prelude::*;

#[allow(unused_imports)]
use crate::model::*;
#[allow(unused_imports)]
use crate::round::*;
use crate::types::{Dir, Rat};

verus! {

/// The IEEE-754 binary64 decomposition of a finite float: `(negative,
/// mantissa, exponent)` denoting `(-1)^negative · mantissa · 2^exponent`.
///
/// `None` for NaN and the infinities.
///
/// **TRUSTED** (`external_body`). Verus has no model of `f64::to_bits`, so the
/// correspondence between the returned triple and the float's real value is an
/// assumption, listed in `TRUSTED.md` and checked by differential tests against
/// `malachite-q`'s exact `Rational::try_from(f64)`.
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

/// Convert an `f64` to a `Rat`, rounding in direction `dir`.
///
/// `None` on NaN, on either infinity, and on `|v| > 2^61` (the specification
/// explicitly permits restricting the magnitude).
///
/// Below `2^-62` in magnitude the value is under the finest grid this crate
/// uses, and the result is the appropriate endpoint of that first grid cell:
/// `0` for `Nearest`, and the neighbouring `±2^-61` for the directed modes that
/// need to stay on their side of the value.
///
/// **Its postcondition is deliberately weak, and that is the trusted boundary
/// showing through.** Verus has no model of `f64`, so no postcondition here can
/// mention `v`'s value at all — R2 and R3 *against the float* are not statable,
/// let alone provable. What is provable is everything downstream of the
/// decomposition, and that lives on [`from_parts_dir`], which this is a
/// two-line composition of. A caller who wants the rounding contract should
/// read it there and add [`f64_decompose`]'s assumption from `TRUSTED.md`.
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

/// The verified core of [`from_f64_dir`]: an IEEE-754 decomposition to a `Rat`,
/// rounded in direction `dir`.
///
/// **This is where the contract lives.** `from_f64_dir` cannot state one, because
/// nothing in Verus relates an `f64` to a rational — that correspondence is the
/// single assumption [`f64_decompose`] carries. Everything *downstream* of the
/// triple is ordinary integer arithmetic, and the module header has always said
/// so; splitting it out is what makes that claim checkable rather than a comment.
///
/// The postcondition is the strongest available: the result is pinned to
/// `round_frac` applied to the exact decomposed rational, which fixes it
/// completely. R2 and R3 against that rational follow from
/// `round::lemma_r2_directed` and `round::lemma_r3_error` (no intra-doc links:
/// items inside `verus!` are not resolvable targets from another module) and
/// are restated below so callers need not re-derive them.
///
/// One postcondition covers all three branches — including the sub-grid one,
/// whose denominator `2^s` with `s > 124` is past what `round_frac_exec` accepts.
/// `round::lemma_round_frac_subgrid` is what closes that gap.
///
/// # The domain is checked at run time as well as proved
///
/// The `requires` below is what a *verified* caller discharges, and
/// [`f64_decompose`]'s postcondition matches it exactly, so `from_f64_dir` gets
/// it for free. But `requires` is ghost: `cargo build` erases it, so it binds
/// nobody outside a `verus!` block, and this function is `pub`. An unverified
/// caller passing `mant` above `2^53` would otherwise reach `mant · 2^e` with
/// `e` up to `64` and overflow `i128` — silently, in any dependent crate built
/// with the default `overflow-checks = false`. The first thing the body does is
/// therefore re-check the same bounds and return `None`, which costs one
/// comparison on a path that already branches and makes the function total for
/// every caller rather than only for the ones Verus can see.
pub fn from_parts_dir(neg: bool, mant: u64, e: i32, dir: Dir) -> (r: Option<Rat>)
    requires
        mant <= 9007199254740992u64,
        -1074 <= e <= 971,
    ensures
        r.is_some() ==> r.unwrap().wf(),
        // The value pin, over the *decomposed* rational.
        r.is_some() ==> r.unwrap() == round_frac(parts_num(neg, mant, e), parts_den(e), dir),
        // R2 and R3, guarded on `!saturated` exactly as the crate's rounding
        // contract is scoped. The guard is discharged rather than assumed for
        // every value this function accepts: `None` is returned above `2^61`,
        // so anything that gets a result is far inside the ceiling.
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
    // The `requires` above, enforced for callers Verus never sees. Dead under
    // verification — which is why the postconditions below are unweakened by it.
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
        }
        return Some(Rat::zero());
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
            // `|±mant · 2^e| == mant · 2^e`. Needed by every branch below, and
            // it is a fact about `abs_int` of a product, so it has to be
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
                // The postcondition wants a *strict* excess over `2^61`, so go
                // through `2^62`: monotonicity alone only gives `<=`.
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
            // 2^117 — far inside i128.
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
            // `-(mant · 2^e) == (-mant) · 2^e` — the sign is applied to the
            // product in the code and to the mantissa in the spec.
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
            // `round_frac_exec` asks for; and |n| <= 2^53 is far below the
            // numerator bound.
            lemma_pow2_mono(s as nat, 124nat);
            lemma_pow2_124();
            lemma_pow2_126();
            lemma_pow2_pos(s as nat);
            assert(n as int == parts_num(neg, mant, e));
            assert(d as int == parts_den(e));
            // `|n| <= 2^53 <= max_mag <= max_mag · d`, since `d >= 1`. On the
            // literals: the mantissa bound is already one, so there is no
            // `pow2(53)` to pin.
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
        // width 2^-61, so `round_frac` would land on that cell's endpoint —
        // which is what `tiny` returns, by `lemma_round_frac_subgrid`.
        proof {
            // `s` is ghost-only here: this branch computes nothing, it just
            // has to show that what `tiny` returns is what `round_frac` would.
            let s = (-e) as nat;
            let n = parts_num(neg, mant, e);
            let d = parts_den(e);
            assert(d == pow2(s));
            lemma_pow2_pos(s);
            lemma_pow2_mono(125nat, s);
            lemma_pow2_125();
            // |n|·2^62 <= 2^53 · 2^62 == 2^115 < 2^125 <= d. Done on the
            // literals rather than through a `pow2(53) + pow2(62)` addition
            // lemma: `2^53` is already a literal here (it is the mantissa
            // bound in the precondition) and `2^62`/`2^125` are pinned, so
            // there is nothing to add.
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
            // `magnitude_fits` — hence `!saturated` — comes back out of the
            // subgrid lemma, which cannot reach `round_frac` without proving it
            // first. Re-deriving it here was the same `nonlinear_arith` block a
            // second time, in a second file.
            lemma_round_frac_subgrid(n, d, dir);
            lemma_r2_r3_directed(n, d, dir);
        }
        Some(tiny(neg, dir))
    }
}

/// The result for a value whose magnitude is strictly below `2^-62`: the
/// correct endpoint of the first dyadic cell.
///
/// Now pinned to `round::subgrid_endpoint`, which
/// `round::lemma_round_frac_subgrid` proves is what `round_frac` would
/// have produced. That equality is the only reason `from_parts_dir` can state
/// one postcondition covering this branch as well as the two that go through
/// the rounder.
///
/// Builds the pair directly rather than through `Rat::new`. `Rat::new` returns an
/// `Option` and would need a canonical-form uniqueness argument to recover the
/// exact representation from `q_is`; `gcd(1, 2^61) == 1` is a one-line
/// discharge of I1 and there is nothing left to reduce.
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
    }
    match dir {
        Dir::Nearest => Rat::zero(),
        Dir::Down => {
            if neg {
                Rat { num: -1, den: eps_den }
            } else {
                Rat::zero()
            }
        },
        Dir::Up => {
            if neg {
                Rat::zero()
            } else {
                Rat { num: 1, den: eps_den }
            }
        },
    }
}

/// Convert a `Rat` to the nearest `f64`.
///
/// **TRUSTED** (`external_body`), and **display/DTO only**. Proving float
/// rounding inside Verus is not worth the effort for a function whose entire
/// job is to hand a number to a JSON encoder. Never feed the result back into
/// `Rat` arithmetic.
///
/// Accuracy: three roundings (numerator, denominator, quotient), so the result
/// is within about `3·2^-53` relative of the true value. The differential test
/// suite pins this at 4 ulp against `malachite-q`.
#[verifier::external_body]
pub fn to_f64(q: Rat) -> f64 {
    (q.num as f64) / (q.den as f64)
}

} // verus!

// ---------------------------------------------------------------------------
// Display and serde — outside the verified region, thin and total
// ---------------------------------------------------------------------------

#[cfg_attr(verus_keep_ghost, verifier::external)]
impl core::fmt::Display for Rat {
    /// `"num/den"`, always in canonical form — so the string is a faithful,
    /// unambiguous rendering of the value.
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}/{}", self.num, self.den)
    }
}

/// Serialise as the `(num, den)` integer pair.
///
/// This round-trips **exactly**, which no `f64` encoding does. The
/// deserialiser re-canonicalises through [`Rat::new`], so a hand-written or
/// corrupted payload cannot produce a `Rat` that violates the type invariant —
/// it produces an error instead.
#[cfg(feature = "serde")]
#[cfg_attr(verus_keep_ghost, verifier::external)]
impl serde::Serialize for Rat {
    fn serialize<S: serde::Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        use serde::ser::SerializeTuple;
        let mut t = s.serialize_tuple(2)?;
        t.serialize_element(&self.num)?;
        t.serialize_element(&self.den)?;
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
// One spelling, shared by all three, rather than two that can drift:
//
//     nan   inf   -inf   >max   <-max
//
// The saturation spellings are deliberately not readable as numbers. Rendering
// `PosSat` as a numeral would be a lie in either direction: the value is
// finite, so `inf` is wrong, and it is unknown, so `4611686018427387903` is
// worse — it would claim an exact value the type explicitly does not have.
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
    /// The denominator was zero.
    ///
    /// Rejected rather than mapped to a special. `Q::new(1, 0)` is `PosInf`
    /// because *a computation* divided by zero and the result has to be some
    /// value; but `"1/0"` in an input stream is a malformed numeral, and
    /// silently accepting it would hide the typo that produced it. `Display`
    /// never emits a zero denominator, so rejecting it costs no round-trip.
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

    /// Parses every spelling [`Display`](core::fmt::Display) produces, so the
    /// round-trip is total over all six states.
    ///
    /// The specials are matched **case-insensitively**, following
    /// `f64::from_str` — IEEE 754 is this type's reference model, and accepting
    /// `"NaN"` alongside `"nan"` costs nothing. Surrounding whitespace is
    /// **rejected**, following `i64::from_str`: a parser that silently trims is
    /// a parser that silently accepts `"1 / 2"` in a data file.
    ///
    /// A bare integer (`"5"`) is accepted as well as a ratio (`"5/1"`), because
    /// it is unambiguous and it is what a human writes.
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
        // `("1", "2/3")`; both fail here, which is the intent.
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

/// `i64::from_str`, with the overflow case distinguished from the malformed one.
///
/// `i64::from_str` rejects a leading `+` on no version this crate supports, so
/// the two error kinds are told apart by re-parsing as `i128`: anything that
/// parses there and not here overflowed.
#[cfg_attr(verus_keep_ghost, verifier::external)]
fn parse_i64(s: &str) -> Result<i64, ParseQError> {
    match s.parse::<i64>() {
        Ok(v) => Ok(v),
        Err(_) => {
            if s.parse::<i128>().is_ok() {
                Err(ParseQError::IntOverflow)
            } else {
                Err(ParseQError::Malformed)
            }
        }
    }
}

/// Serialise a number as the `(num, den)` pair and a special as its string.
///
/// This is the untagged shape from issue #26 §8, and it carries that section's
/// caveat: **it works only in self-describing formats.** The deserialiser has to
/// ask the format what kind of value comes next, so `bincode` and other
/// non-self-describing codecs will fail at runtime rather than at compile time.
/// #26 §12 leaves the "is a wire break acceptable?" question open; if
/// non-self-describing formats must keep working, this needs to become an
/// externally tagged representation, which breaks the existing `Rat` wire format.
///
/// `Rat`'s own serde impl is untouched by this — a bare `Rat` still round-trips
/// exactly as it did.
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
                // Exact match, not the case-insensitive `FromStr` spelling: a
                // wire format is machine-written, so a case variant means an
                // encoder disagreed with this one and should be caught, not
                // absorbed.
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
                // Re-canonicalises through `Rat::new`, exactly as `Rat`'s own
                // deserialiser does, so `[2, 4]` is accepted as `1/2`. A payload
                // that cannot be canonicalised is an error rather than a
                // saturation: on the wire, an unrepresentable pair means the
                // producer and this type disagree, which is worth surfacing.
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
