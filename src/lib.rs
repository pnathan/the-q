//! Verified bounded rational arithmetic, checked by [Verus](https://github.com/verus-lang/verus).
//!
//! The central type is [`Q`], a rational `num/den` held in canonical form
//! (`den > 0`, `gcd(|num|, den) == 1`) with both magnitudes bounded by
//! `2^62 - 1`. Arithmetic is exact whenever the exact reduced result fits
//! that budget; otherwise the result is rounded to a dyadic grid with a
//! machine-checked directed-rounding contract (error `<= 2^-60 * max(1, |x|)`).
//!
//! See `TRUSTED.md` for the (very small) trusted surface.

#![forbid(unsafe_code)]

pub mod specs;
pub mod gcd;
pub mod q;
