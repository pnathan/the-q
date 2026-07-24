//! `the-q`: bounded, canonical rational arithmetic with a verified-rounding
//! design (Verus proof pending -- see `TRUSTED.md` and the crate README).
//!
//! `Q` represents a rational number `num / den` in **canonical form**
//! (`den > 0`, `gcd(|num|, den) == 1`) with both fields bounded to
//! `[-(2^62 - 1), 2^62 - 1]`. Arithmetic is exact whenever the exact
//! reduced result fits that budget (R1), and falls back to directed
//! dyadic rounding with a proven-in-tests error bound of `2^-60` otherwise
//! (R2-R4). See the `rounding` module docs for the full contract.
//!
//! Canonical form gives structural equality == mathematical equality, so
//! `Eq`, `Hash`, and `Ord` are all meaningful and `Q` is a plain `Copy`
//! 128-bit value type (no heap, trivially `Send + Sync`).

mod convert;
mod interval;
mod nary;
mod ops;
mod q;
mod rounding;

#[cfg(feature = "serde")]
mod serde_impl;

pub use convert::{from_f64_dir, to_f64, Dir};
pub use interval::QI;
pub use nary::{product, sum, weighted_mean};
pub use ops::{abs, add, clamp, div, max, min, mul, neg, recip, sub};
pub use q::Q;
pub use rounding::MAX_MAGNITUDE;

/// [`QI`]-specific arithmetic (spec M6, stretch): a directed-rounding
/// interval type over `Q`. Kept in its own sub-module rather than the crate
/// root namespace since `add`/`sub`/`mul`/`div`/`min`/`max`/`neg` would
/// otherwise collide with the identically-named `Q` operations above.
pub mod interval_ops {
    pub use crate::interval::{add, div, max, min, mul, neg, sub};
}
