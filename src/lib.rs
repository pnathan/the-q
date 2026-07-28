//! # `the-q` — verified bounded rational arithmetic
//!
//! `Q` is an exact rational number `num / den` held in two `i64` fields, kept in
//! canonical form (`den > 0`, `gcd(|num|, den) == 1`) and bounded by a fixed
//! width budget (`|num| <= 2^62 - 1`, `den <= 2^62 - 1`).
//!
//! Arithmetic is *exact whenever the exact result fits the budget* and
//! *verifiably rounded* when it does not. Every intermediate is computed in
//! `i128`, and the 2^62 budget is chosen precisely so that no `i128`
//! intermediate can overflow (see [`crate::round`] and `docs/SPEC.md` §1).
//!
//! ```
//! use the_q::{Dir, Q};
//!
//! // Short decimals — the engine's ingestion path — are exact, not approximate.
//! let reliability = Q::from_decimal(85, 2).unwrap();   // 0.85 == 17/20
//! let weight = Q::from_decimal(3, 1).unwrap();         // 0.3  == 3/10
//! let combined = Q::mul(reliability, weight);
//! assert_eq!(combined.to_string(), "51/200");
//!
//! // The order is a total order: no NaN, so no incomparable pairs.
//! assert!(combined < reliability);
//! assert!(combined.in_unit_interval());
//!
//! // Directed modes bracket the exact value, which is what the interval layer
//! // is built on.
//! let a = Q::new(1, 3).unwrap();
//! assert!(Q::le(Q::mul_dir(a, a, Dir::Down), Q::mul_dir(a, a, Dir::Up)));
//! ```
//!
//! ## Design in one paragraph
//!
//! Subjective-logic fusion is rational-closed, so `f64` throws away exactness
//! for nothing; but exact `ℚ` denominators grow without bound under long fusion
//! chains, and a *verified* arbitrary-precision bignum does not exist in the
//! Verus ecosystem. The middle road is a bounded rational with a proven
//! rounding contract: computations that stay inside the budget are bit-exact
//! and order-independent, and computations that leave it carry a machine-stated
//! error bound of `2^-61 · max(1, |exact|)` per operation instead of `f64`
//! folklore.
//!
//! ## Honesty notes (read these)
//!
//! * With rounding, [`Q::add`] and [`Q::mul`] are **commutative** but **not
//!   associative in general**. Associativity and distributivity hold on the
//!   *exact path* — i.e. whenever no intermediate rounds. See `README.md`.
//! * The composed operation ("exact if it fits, else snap to the dyadic grid")
//!   is **not globally monotone**; the *rounding step itself* is (R4 is stated
//!   per-grid, as the specification permits). `README.md` carries the
//!   counterexample.
//! * Magnitude overflow (an exact result with `|value| > 2^62 - 1`) is placed
//!   **outside** the R3 contract by choice, not by necessity — some such values
//!   do have a `Q` within the bound. Those results **saturate**, and the
//!   `checked_*` variants report them as `None`. No engine value comes near
//!   this ceiling.
//!
//! ## Verification
//!
//! Specifications and proofs are written in [Verus](https://github.com/verus-lang/verus).
//! `cargo build` uses plain rustc (ghost code erased); `verus verify` checks the
//! same sources. See `VERIFICATION.md` for the obligation map (V1–V8) and
//! `TRUSTED.md` for the enumerated trusted boundary.

#![allow(clippy::needless_range_loop)]
#![allow(clippy::comparison_chain)]
// Verus's surface language does not accept compound-assignment operators or
// `RangeInclusive::contains` in exec code, and the inherent `Q::add`/`Q::mul`
// names are deliberate (the operator traits delegate to them and are not
// callable from verified code).
#![allow(clippy::assign_op_pattern)]
#![allow(clippy::should_implement_trait)]
#![allow(clippy::manual_range_contains)]
#![allow(clippy::unusual_byte_groupings)]
#![allow(clippy::manual_div_ceil)]
#![allow(clippy::implicit_saturating_sub)]

// Verus's macro machinery.
#[allow(unused_imports)]
use verus_builtin as _;
#[allow(unused_imports)]
use vstd as _;

pub mod model;
pub mod types;

pub mod gcd;
pub mod round;
pub mod saturation;

pub mod q;

pub mod convert;
pub mod interval;
pub mod laws;
pub mod lipschitz;
pub mod nary;

pub use convert::{from_f64_dir, to_f64};
pub use interval::QI;
pub use types::{Dir, MAX_DEC_PLACES, MAX_MAG, Q};
