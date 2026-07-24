// the-q: exact-with-verified-rounding rational arithmetic
// Invariants: I1 (canonical, gcd=1, den>0) and I2 (|num|,den ≤ 2^62-1) on every Q.
// Proof obligations V1-V6 are discharged by Verus; see each module.

pub mod gcd;
pub mod q;
pub mod round;
pub mod convert;

#[cfg(feature = "serde")]
pub mod serde_impl;

pub use q::{Q, Dir};
pub use convert::from_decimal;
