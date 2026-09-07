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
use crate::types::{Dir, Rat};

verus! {

/// The IEEE-754 fields of a finite float, `(negative, mantissa, exponent)`;
/// `None` for NaN and infinities. TRUSTED: Verus has no model of `to_bits`.
///
/// Public only because Verus's visibility rules require it; not semver-stable.
///
/// ```
/// use the_q::convert::f64_decompose;
///
/// assert_eq!(f64_decompose(1.0f64), Some((false, 4503599627370496u64, -52)));
/// assert_eq!(f64_decompose(f64::NAN), None);
/// ```
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
///
/// ```
/// use the_q::{Rat, Dir, from_f64_dir};
///
/// assert_eq!(from_f64_dir(0.5, Dir::Nearest), Some(Rat::new(1, 2).unwrap()));
/// assert_eq!(from_f64_dir(f64::NAN, Dir::Nearest), None);
/// assert_eq!(from_f64_dir(f64::INFINITY, Dir::Nearest), None);
/// ```
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
///
/// Public only because Verus's visibility rules require it; not semver-stable.
///
/// ```
/// use the_q::Dir;
/// use the_q::convert::from_parts_dir;
///
/// // 1 * 2^0 == 1.
/// assert_eq!(from_parts_dir(false, 1, 0, Dir::Nearest).unwrap().to_string(), "1/1");
/// ```
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
///
/// Public only because Verus's visibility rules require it; not semver-stable.
///
/// ```
/// use the_q::Dir;
/// use the_q::convert::tiny;
///
/// let up = tiny(false, Dir::Up);
/// assert_eq!(up.to_string(), "1/2305843009213693952");
/// ```
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
///
/// ```
/// use the_q::{Rat, to_f64};
///
/// assert_eq!(to_f64(Rat::new(1, 2).unwrap()), 0.5);
/// ```
#[verifier::external_body]
pub fn to_f64(q: Rat) -> f64 {
    (q.numerator() as f64) / (q.denominator() as f64)
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
///
/// ```
/// use the_q::{Q, Rat, q_from_f64};
///
/// assert_eq!(q_from_f64(0.5), Q::Number(Rat::new(1, 2).unwrap()));
/// assert_eq!(q_from_f64(f64::NAN), Q::Nan);
/// assert_eq!(q_from_f64(f64::INFINITY), Q::PosInf);
/// ```
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
