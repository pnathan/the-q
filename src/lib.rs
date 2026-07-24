// the-q: exact-with-verified-rounding rational arithmetic.
// Invariants enforced on every Q value:
//   I1 (canonical): den > 0, gcd(|num|, den) = 1, num == 0 => den == 1
//   I2 (bounded):   |num| ≤ 2^62−1 and den ≤ 2^62−1
//
// Proof obligations V1–V8 (see TRUSTED.md and each module's verus! blocks).

pub(crate) mod gcd;
pub mod q;
pub(crate) mod round;
pub mod convert;
pub mod laws;

#[cfg(feature = "serde")]
pub mod serde_impl;

pub use q::{Q, Dir, BOUND};
