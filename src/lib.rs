//! # `the-q` — verified bounded rational arithmetic
//!
//! `Rat` is an exact rational number `num / den` held in two `i64` fields, kept in
//! canonical form (`den > 0`, `gcd(|num|, den) == 1`) and bounded by a fixed
//! width budget (`|num| <= 2^62 - 1`, `den <= 2^62 - 1`).
//!
//! Arithmetic is *exact whenever the exact result fits the budget* and
//! *verifiably rounded* when it does not. Every intermediate is computed in
//! `i128`, and the 2^62 budget is chosen precisely so that no `i128`
//! intermediate can overflow (see [`crate::round`] and `docs/SPEC.md` §1).
//!
//! ```
//! use the_q::{Dir, Rat};
//!
//! // Short decimals — the engine's ingestion path — are exact, not approximate.
//! let reliability = Rat::from_decimal(85, 2).unwrap();   // 0.85 == 17/20
//! let weight = Rat::from_decimal(3, 1).unwrap();         // 0.3  == 3/10
//! let combined = Rat::mul(reliability, weight);
//! assert_eq!(combined.to_string(), "51/200");
//!
//! // The order is a total order: no NaN, so no incomparable pairs.
//! assert!(combined < reliability);
//! assert!(combined.in_unit_interval());
//!
//! // Directed modes bracket the exact value, which is what the interval layer
//! // is built on.
//! let a = Rat::new(1, 3).unwrap();
//! assert!(Rat::le(Rat::mul_dir(a, a, Dir::Down), Rat::mul_dir(a, a, Dir::Up)));
//! ```
//!
//! ## `Rat` and `Q`
//!
//! [`Rat`] above is the verified kernel: exact, canonical, bounded — and
//! *partial*. `Rat::new(_, 0)` is `None`, `Rat::div(x, 0)` panics, and
//! `Rat::add(MAX_MAG, MAX_MAG)` silently returns `MAX_MAG`.
//!
//! [`Q`] is an extension layer over that kernel which makes "not a representable
//! rational" an explicit, observable state instead of something the caller is
//! trusted to have ruled out. Arithmetic on it is **total**: every operation on
//! every input returns a value in the type, and no operation panics.
//!
//! ```
//! use the_q::{Q, Rat};
//!
//! // Division by zero is a value, not a panic. IEEE 754 is the reference model.
//! assert_eq!(Q::div(Q::one(), Q::zero()), Q::PosInf);
//! assert_eq!(Q::div(Q::zero(), Q::zero()), Q::Nan);
//! assert_eq!(Q::checked_div(Q::one(), Q::zero()), None);
//!
//! // Overflow is reported, not clamped — and it is distinguishable from a
//! // division by zero, which is what the two separate state families buy you.
//! let m = Q::Number(Rat::new(the_q::MAX_MAG, 1).unwrap());
//! let over = Q::add(m, m);
//! assert!(over.is_saturated() && !over.is_infinite());
//! assert_eq!(over.to_string(), ">max");
//!
//! // Saturation denotes finite reals only, so this is exact where `0 * inf`
//! // would be indeterminate.
//! assert_eq!(Q::mul(Q::zero(), Q::PosSat), Q::zero());
//! assert_eq!(Q::mul(Q::zero(), Q::PosInf), Q::Nan);
//!
//! // The order is total, so `Q` can be a map key or be sorted directly.
//! let mut v = vec![Q::Nan, Q::PosInf, Q::zero(), Q::NegInf];
//! v.sort();
//! assert_eq!(v, vec![Q::NegInf, Q::zero(), Q::PosInf, Q::Nan]);
//!
//! // But selection propagates Nan, and therefore deliberately disagrees with
//! // `Ord`-based selection. A fold of `Q::min` is not `slice.iter().min()`.
//! assert_eq!(Q::min(Q::Nan, Q::one()), Q::Nan);
//! assert_eq!([Q::Nan, Q::one()].into_iter().min().unwrap(), Q::one());
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
//! * With rounding, [`Rat::add`] and [`Rat::mul`] are **commutative** but **not
//!   associative in general**. Associativity and distributivity hold on the
//!   *exact path* — i.e. whenever no intermediate rounds. See `README.md`.
//! * The composed operation ("exact if it fits, else snap to the dyadic grid")
//!   is **not globally monotone**; the *rounding step itself* is (R4 is stated
//!   per-grid, as the specification permits). `README.md` carries the
//!   counterexample.
//! * Magnitude overflow (an exact result with `|value| > 2^62 - 1`) is placed
//!   **outside** the R3 contract by choice, not by necessity — some such values
//!   do have a `Rat` within the bound. Those results **saturate**, and the
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
// `RangeInclusive::contains` in exec code, and the inherent `Rat::add`/`Rat::mul`
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
pub mod ext;
pub mod interval;
pub mod laws;
pub mod lipschitz;
pub mod nary;
pub mod transcendental;

pub use convert::{from_f64_dir, q_from_f64, to_f64, ParseQError};
pub use ext::{Sign, Q};
pub use interval::QI;
pub use types::{Dir, Rat, MAX_DEC_PLACES, MAX_MAG};
