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
//!   into `Q` arithmetic; that would silently reintroduce every `f64` problem
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
use crate::types::{Dir, Q};

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

/// Convert an `f64` to a `Q`, rounding in direction `dir`.
///
/// `None` on NaN, on either infinity, and on `|v| > 2^61` (the specification
/// explicitly permits restricting the magnitude).
///
/// Below `2^-62` in magnitude the value is under the finest grid this crate
/// uses, and the result is the appropriate endpoint of that first grid cell:
/// `0` for `Nearest`, and the neighbouring `±2^-61` for the directed modes that
/// need to stay on their side of the value.
pub fn from_f64_dir(v: f64, dir: Dir) -> (r: Option<Q>)
    ensures
        r.is_some() ==> r.unwrap().wf(),
{
    let parts = f64_decompose(v);
    match parts {
        None => None,
        Some((neg, mant, e)) => {
            if mant == 0 {
                return Some(Q::zero());
            }
            proof {
                lemma_pow2_61();
                lemma_pow2_62();
                lemma_pow2_124();
                lemma_pow2_126();
            }
            if e >= 0 {
                if e > 64 {
                    // mant >= 2^52 here, so the value exceeds 2^61 outright.
                    return None;
                }
                let p: i128 = pow2_i128(e as u32);
                proof {
                    // mant <= 2^53 and p == 2^e <= 2^64, so the product is at
                    // most 2^117 — far inside i128.
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
                    // d == 2^s with s <= 124, which is exactly the denominator
                    // bound `round_frac_exec` asks for; and |n| <= 2^53 is far
                    // below the numerator bound.
                    lemma_pow2_mono(s as nat, 124nat);
                    lemma_pow2_124();
                    lemma_pow2_126();
                }
                Some(round_frac_exec(n, d, dir))
            } else {
                // |v| <= 2^53 · 2^-125 == 2^-72, strictly inside the first grid
                // cell of width 2^-61.
                Some(tiny(neg, dir))
            }
        },
    }
}

/// The result for a value whose magnitude is strictly below `2^-62`: the
/// correct endpoint of the first dyadic cell.
pub fn tiny(neg: bool, dir: Dir) -> (r: Q)
    ensures
        r.wf(),
{
    let eps_den: i64 = 2305843009213693952;  // 2^61
    match dir {
        Dir::Nearest => Q::zero(),
        Dir::Down => {
            if neg {
                let q = Q::new(-1, eps_den);
                match q {
                    Some(x) => x,
                    None => Q::zero(),
                }
            } else {
                Q::zero()
            }
        },
        Dir::Up => {
            if neg {
                Q::zero()
            } else {
                let q = Q::new(1, eps_den);
                match q {
                    Some(x) => x,
                    None => Q::zero(),
                }
            }
        },
    }
}

/// Convert a `Q` to the nearest `f64`.
///
/// **TRUSTED** (`external_body`), and **display/DTO only**. Proving float
/// rounding inside Verus is not worth the effort for a function whose entire
/// job is to hand a number to a JSON encoder. Never feed the result back into
/// `Q` arithmetic.
///
/// Accuracy: three roundings (numerator, denominator, quotient), so the result
/// is within about `3·2^-53` relative of the true value. The differential test
/// suite pins this at 4 ulp against `malachite-q`.
#[verifier::external_body]
pub fn to_f64(q: Q) -> f64 {
    (q.num as f64) / (q.den as f64)
}

} // verus!

// ---------------------------------------------------------------------------
// Display and serde — outside the verified region, thin and total
// ---------------------------------------------------------------------------

#[cfg_attr(verus_keep_ghost, verifier::external)]
impl core::fmt::Display for Q {
    /// `"num/den"`, always in canonical form — so the string is a faithful,
    /// unambiguous rendering of the value.
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}/{}", self.num, self.den)
    }
}

/// Serialise as the `(num, den)` integer pair.
///
/// This round-trips **exactly**, which no `f64` encoding does. The
/// deserialiser re-canonicalises through [`Q::new`], so a hand-written or
/// corrupted payload cannot produce a `Q` that violates the type invariant —
/// it produces an error instead.
#[cfg(feature = "serde")]
#[cfg_attr(verus_keep_ghost, verifier::external)]
impl serde::Serialize for Q {
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
impl<'de> serde::Deserialize<'de> for Q {
    fn deserialize<D: serde::Deserializer<'de>>(d: D) -> Result<Q, D::Error> {
        use serde::de::Error;
        let (num, den) = <(i64, i64) as serde::Deserialize>::deserialize(d)?;
        Q::new(num, den).ok_or_else(|| {
            D::Error::custom("the-q: (num, den) pair is not a representable rational")
        })
    }
}
