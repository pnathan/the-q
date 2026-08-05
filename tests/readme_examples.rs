//! The README's code examples. This file compiles and runs them.
//!
//! The crate does not include the README via `#![doc = include_str!(...)]`.
//! The README examples are therefore not doctests. Without this file, nothing
//! detects drift between those examples and the API. This file reproduces them
//! verbatim.

use the_q::{Rat, MAX_MAG, Q};

#[test]
fn readme_kernel_example() {
    let reliability = Rat::from_decimal(85, 2).unwrap(); // 0.85, exactly — 17/20
    let weight = Rat::from_decimal(3, 1).unwrap(); // 0.3,  exactly — 3/10
    let combined = Rat::mul(reliability, weight); // 51/200, exactly
    assert_eq!(combined.to_string(), "51/200");
}

#[test]
fn readme_extended_example() {
    assert_eq!(Q::div(Q::one(), Q::zero()), Q::PosInf); // not a panic
    assert_eq!(Q::div(Q::zero(), Q::zero()), Q::Nan);
    assert_eq!(Q::checked_div(Q::one(), Q::zero()), None); // what std does

    let m = Q::Number(Rat::new(MAX_MAG, 1).unwrap());
    assert!(Q::add(m, m).is_saturated()); // reported, not clamped
}

#[test]
fn readme_claims_about_the_kernel_defects_hold() {
    // The README states these as facts about `Rat`. If any one stops holding,
    // the README is wrong and this test fails.
    let zero = Rat::new(0, 1).unwrap();
    let one = Rat::new(1, 1).unwrap();
    assert!(Rat::new(1, 0).is_none(), "Rat::new(_, 0) is None");
    assert!(std::panic::catch_unwind(|| Rat::div(one, zero)).is_err());
    let broken = zero.recip();
    assert_eq!((broken.numerator(), broken.denominator()), (-1, 0));
    let m = Rat::new(MAX_MAG, 1).unwrap();
    assert_eq!(Rat::add(m, m).numerator(), MAX_MAG);
}

#[test]
fn readme_claims_about_the_extended_type_hold() {
    // "Number(0) * PosSat is exactly Number(0), where 0 * inf is indeterminate"
    assert_eq!(Q::mul(Q::zero(), Q::PosSat), Q::zero());
    assert_eq!(Q::mul(Q::zero(), Q::PosInf), Q::Nan);
    // "Nan == Nan is true, and Nan sorts last"
    assert_eq!(Q::Nan, Q::Nan);
    let mut v = [Q::Nan, Q::PosInf, Q::NegInf];
    v.sort();
    assert_eq!(*v.last().unwrap(), Q::Nan);
    // "a fold of Q::min is not slice.iter().min()"
    assert_eq!(Q::min(Q::Nan, Q::one()), Q::Nan);
    assert_eq!([Q::Nan, Q::one()].into_iter().min().unwrap(), Q::one());
    // "is_saturated means overflow, is_infinite means division by zero"
    assert!(!Q::PosSat.is_infinite() && !Q::PosInf.is_saturated());
    // "there is deliberately no is_finite()". A saturated value is finite.
    assert!(!Q::PosSat.is_number());
}
