//! # `the-q` — verified bounded rational arithmetic
//!
//! [`Rat`] is `num / den` in two `i64` fields, canonical (`den > 0`,
//! `gcd(|num|, den) == 1`) and bounded (`|num|, den <= 2^62 - 1`). Arithmetic
//! is exact when the exact result fits and rounded to a proven contract when it
//! does not; every intermediate is `i128` and cannot overflow.
//!
//! ```
//! use the_q::{Dir, Rat};
//!
//! let reliability = Rat::from_decimal(85, 2).unwrap();   // 0.85 == 17/20
//! let weight = Rat::from_decimal(3, 1).unwrap();         // 0.3  == 3/10
//! let combined = Rat::mul(reliability, weight);
//! assert_eq!(combined.to_string(), "51/200");
//! assert!(combined < reliability);
//!
//! // Directed modes bracket the exact value.
//! let a = Rat::new(1, 3).unwrap();
//! assert!(Rat::le(Rat::mul_dir(a, a, Dir::Down), Rat::mul_dir(a, a, Dir::Up)));
//! ```
//!
//! `Rat` is partial: `Rat::new(_, 0)` is `None`, `Rat::div(x, 0)` panics, and
//! an over-budget result saturates. [`Q`] makes each of those a value and is
//! total: every operation on every input returns a `Q` and nothing panics.
//!
//! ```
//! use the_q::{Q, Rat};
//!
//! assert_eq!(Q::div(Q::one(), Q::zero()), Q::PosInf);
//! assert_eq!(Q::div(Q::zero(), Q::zero()), Q::Nan);
//! assert_eq!(Q::checked_div(Q::one(), Q::zero()), None);
//!
//! // Overflow is reported, and is distinct from division by zero.
//! let m = Q::Number(Rat::new(the_q::MAX_MAG, 1).unwrap());
//! let over = Q::add(m, m);
//! assert!(over.is_saturated() && !over.is_infinite());
//! assert_eq!(over.to_string(), ">max");
//!
//! // Saturation denotes finite reals, so this is exact where `0 * inf` is not.
//! assert_eq!(Q::mul(Q::zero(), Q::PosSat), Q::zero());
//! assert_eq!(Q::mul(Q::zero(), Q::PosInf), Q::Nan);
//!
//! // The order is total; `Nan` sorts last. Selection propagates `Nan`, so a
//! // fold of `Q::min` is not `iter().min()`.
//! let mut v = vec![Q::Nan, Q::PosInf, Q::zero(), Q::NegInf];
//! v.sort();
//! assert_eq!(v, vec![Q::NegInf, Q::zero(), Q::PosInf, Q::Nan]);
//! assert_eq!(Q::min(Q::Nan, Q::one()), Q::Nan);
//! ```
//!
//! ## Limits
//!
//! * The rounding bound `2^-61 · max(1, |exact|)` is absolute below 1.
//! * With rounding, `add` and `mul` are commutative but not associative;
//!   associativity holds on the exact path and the defect is bounded.
//! * Rounding is monotone on each grid, not across the representable/rounded
//!   boundary. `README.md` has the counterexample.
//!
//! ## Verification and API stability
//!
//! Proofs are in the source inside `verus!` blocks; `cargo verus verify`
//! checks them, `cargo build` erases them. `VERIFICATION.md` maps the
//! obligations, `TRUSTED.md` lists the three trusted functions.
//!
//! [`Rat`], [`Q`], [`Dir`], [`interval::QI`], their operations and constructors,
//! and [`nary`] follow semver. Other public items (`gcd`, `model`, `round`,
//! `lipschitz`, `fx`, and executable helpers such as
//! `round::round_frac_exec_with_gcd`) are public because Verus's visibility
//! rules require it and may change shape in patch releases.

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

pub mod fx;
pub mod gcd;
pub mod round;
pub mod saturation;

pub mod q;

pub mod convert;
pub mod denote;
pub mod exact;
pub mod ext;
pub mod interval;
pub mod laws;
pub mod laws_q;
pub mod lipschitz;
pub mod soundness;
pub mod soundness_mul;
pub mod nary;
pub mod transcendental;

pub use convert::{ParseQError, from_f64_dir, q_from_f64, to_f64};
pub use exact::{Exact, ExactError};
pub use ext::{Q, Sign};
pub use interval::QI;
pub use types::{Dir, MAX_DEC_PLACES, MAX_MAG, Rat};
