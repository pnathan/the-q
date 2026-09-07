//! The `fixed` boundary (issue #33 follow-up): any 128-bit-backed
//! `fixed::types::I*F*` alias (`Bits = i128`) converts through the generic
//! `from_fixed_dir`/`from_fixed_exact`/`q_from_fixed`/`exact_from_fixed`,
//! built on the shared `from_ratio128_dir`/`from_ratio128_exact` core.
//! `I16F16` and similarly narrow aliases are backed by `FixedI32`/`FixedI64`,
//! not `i128`, so they do not satisfy `Fixed<Bits = i128>` and cannot appear
//! in these tests at all -- only the widest (128-bit total) family can.

#![cfg(feature = "fixed")]

use fixed::types::{I32F96, I64F64};
use the_q::{Dir, Exact, ExactError, Q, Rat, exact_from_fixed, from_fixed_dir, q_from_fixed};

#[test]
fn small_value_is_exact() {
    let v = I64F64::from_num(3.5);
    let r = from_fixed_dir(v, Dir::Nearest).unwrap();
    assert_eq!(r, Rat::new(7, 2).unwrap());
}

#[test]
fn zero_is_zero() {
    let v = I64F64::from_num(0);
    assert_eq!(from_fixed_dir(v, Dir::Nearest).unwrap(), Rat::zero());
}

#[test]
fn negative_value_is_exact() {
    let v = I64F64::from_num(-1.25);
    let r = from_fixed_dir(v, Dir::Nearest).unwrap();
    assert_eq!(r, Rat::new(-5, 4).unwrap());
}

#[test]
fn generic_over_different_frac_widths_agree_on_the_same_value() {
    // 1.5 represented with 64 and with 96 fractional bits must denote the
    // same `Rat`: the generic function does not care how the caller chose
    // to split the 128 bits between integer and fractional parts.
    let a = from_fixed_dir(I64F64::from_num(1.5), Dir::Nearest).unwrap();
    let b = from_fixed_dir(I32F96::from_num(1.5), Dir::Nearest).unwrap();
    assert_eq!(a, b);
}

#[test]
fn q_saturates_a_huge_value() {
    // i64::MAX (~9.2e18) is past MAX_MAG (2^62 - 1, ~4.6e18), and still well
    // inside I64F64's 64-bit signed integer part.
    let huge = I64F64::from_num(i64::MAX);
    assert_eq!(q_from_fixed(huge), Q::PosSat);
    assert_eq!(q_from_fixed(-huge), Q::NegSat);
}

#[test]
fn q_does_not_saturate_a_value_within_budget() {
    let v = I64F64::from_num(12345);
    assert_eq!(q_from_fixed(v), Q::Number(Rat::new(12345, 1).unwrap()));
}

#[test]
fn exact_matches_dir_when_it_fits() {
    let v = I64F64::from_num(-1.25);
    let via_exact = exact_from_fixed(v).unwrap();
    assert_eq!(via_exact, Exact::new(Rat::new(-5, 4).unwrap()));
}

#[test]
fn exact_refuses_what_dir_would_saturate() {
    let huge = I64F64::from_num(i64::MAX);
    assert_eq!(exact_from_fixed(huge), Err(ExactError::Inexact));
}
