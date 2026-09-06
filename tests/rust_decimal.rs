//! The `rust_decimal` boundary (issue #33).
//!
//! `Decimal` stores `mantissa · 10^-scale` exactly (`scale() <= 28`,
//! `|mantissa()| <= 2^96 - 1`), so `from_rust_decimal_dir` is total on it and
//! exact whenever the reduced `(mantissa, 10^scale)` pair fits the width
//! budget. These tests check that path, its agreement with the crate's
//! existing exact-decimal ingestion (`Rat::from_decimal`), and the two
//! failure modes: directed rounding past the exact grid, and saturation past
//! the budget entirely.

#![cfg(feature = "rust_decimal")]

use rust_decimal::Decimal;
use the_q::{Dir, MAX_DECIMAL_MANTISSA, Q, Rat, from_rust_decimal_dir, q_from_rust_decimal};

#[test]
fn small_decimal_is_exact_and_reduced() {
    // 0.85 == 85/100 == 17/20.
    let d = Decimal::new(85, 2);
    let r = from_rust_decimal_dir(d, Dir::Nearest);
    assert_eq!(r, Rat::new(17, 20).unwrap());
}

#[test]
fn negative_scale_zero_is_the_integer() {
    let d = Decimal::new(-7, 0);
    let r = from_rust_decimal_dir(d, Dir::Nearest);
    assert_eq!(r, Rat::new(-7, 1).unwrap());
}

#[test]
fn agrees_with_the_existing_exact_decimal_path() {
    // For any `(mantissa, dec_places)` that `Rat::from_decimal` already
    // accepts (`|mantissa| <= MAX_MAG`, `dec_places <= 18`), the two
    // ingestion paths denote the same value: both are exact, and R1 pins the
    // exact-path result uniquely, so equality is not a coincidence.
    for mantissa in [
        0i64,
        1,
        -1,
        12345,
        -999999,
        i64::from(u32::MAX),
        -(i64::from(u32::MAX)),
    ] {
        for dec_places in [0u8, 1, 2, 6, 18] {
            let via_decimal = Decimal::new(mantissa, u32::from(dec_places));
            let via_rat = Rat::from_decimal(mantissa, dec_places).unwrap();
            assert_eq!(
                from_rust_decimal_dir(via_decimal, Dir::Nearest),
                via_rat,
                "mantissa={mantissa}, dec_places={dec_places}"
            );
        }
    }
}

#[test]
fn rounds_when_the_reduced_pair_leaves_the_budget() {
    // An odd mantissa at the maximum scale is coprime to 10, so the reduced
    // denominator stays at 10^28, far past `MAX_MAG`: this is on the R2/R3
    // snap path, not the exact one, and directed rounding must bracket it.
    let d = Decimal::from_i128_with_scale(MAX_DECIMAL_MANTISSA, 28);
    let down = from_rust_decimal_dir(d, Dir::Down);
    let up = from_rust_decimal_dir(d, Dir::Up);
    assert!(down <= up);
    // The value is about 7.92, so neither endpoint saturates to the budget's
    // ceiling; both are small, ordinary rationals.
    assert!(down.numerator() > 0);
    assert!(up.numerator() > 0);
}

#[test]
fn saturates_at_the_extreme_like_f64_does() {
    assert_eq!(q_from_rust_decimal(Decimal::MAX), Q::PosSat);
    assert_eq!(q_from_rust_decimal(Decimal::MIN), Q::NegSat);
}

#[test]
fn from_impl_matches_the_named_function() {
    let d = Decimal::new(-31415, 4);
    assert_eq!(Q::from(d), q_from_rust_decimal(d));
}

#[test]
fn zero_is_zero_at_every_scale() {
    for scale in [0u32, 1, 18, 28] {
        let d = Decimal::new(0, scale);
        assert_eq!(from_rust_decimal_dir(d, Dir::Nearest), Rat::zero());
    }
}
