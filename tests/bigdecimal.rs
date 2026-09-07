//! The `bigdecimal` boundary (issue #33 follow-up): `BigDecimal` is
//! `digits · 10^-scale` with an arbitrary-precision `digits` and an `i64`
//! `scale` that, unlike `rust_decimal::Decimal`'s, may be negative
//! (`digits · 10^|scale|`). Built on the shared `from_ratio128_dir`/
//! `from_ratio128_exact` core once normalised to a nonnegative scale and a
//! fallible `i128` extraction.

#![cfg(feature = "bigdecimal")]

use bigdecimal::BigDecimal;
use std::str::FromStr;
use the_q::{
    Dir, Exact, ExactError, Q, Rat, exact_from_bigdecimal, from_bigdecimal_dir,
    from_bigdecimal_exact, q_from_bigdecimal,
};

#[test]
fn small_value_is_exact() {
    let v = BigDecimal::from_str("0.85").unwrap();
    let r = from_bigdecimal_dir(&v, Dir::Nearest).unwrap();
    assert_eq!(r, Rat::new(17, 20).unwrap());
    assert_eq!(from_bigdecimal_exact(&v).unwrap(), r);
}

#[test]
fn negative_scale_is_a_large_integer() {
    // bigdecimal represents "1.2e3" as digits=12, scale=-2, i.e. 12 * 10^2.
    let v = BigDecimal::from_str("1.2e3").unwrap();
    let r = from_bigdecimal_dir(&v, Dir::Nearest).unwrap();
    assert_eq!(r, Rat::new(1200, 1).unwrap());
}

#[test]
fn zero_is_zero() {
    let v = BigDecimal::from_str("0").unwrap();
    assert_eq!(from_bigdecimal_dir(&v, Dir::Nearest).unwrap(), Rat::zero());
}

#[test]
fn negative_value_is_exact() {
    let v = BigDecimal::from_str("-3.14").unwrap();
    let r = from_bigdecimal_dir(&v, Dir::Nearest).unwrap();
    assert_eq!(r, Rat::new(-157, 50).unwrap());
}

#[test]
fn too_many_digits_for_i128_is_none_but_q_falls_back_to_f64() {
    // 40 nines after the point: the digits alone (all 9s, 40 of them) don't
    // fit an i128, even though the value is comfortably inside [0, 1).
    let v = BigDecimal::from_str(&format!("0.{}", "9".repeat(40))).unwrap();
    assert_eq!(from_bigdecimal_dir(&v, Dir::Nearest), None);
    assert_eq!(from_bigdecimal_exact(&v), None);
    assert_eq!(exact_from_bigdecimal(&v), Err(ExactError::Inexact));
    match q_from_bigdecimal(&v) {
        Q::Number(r) => {
            // Indistinguishable from 1 at f64 precision, let alone this
            // crate's grid.
            assert_eq!(r, Rat::one());
        }
        other => panic!("expected a number close to 1, got {other}"),
    }
}

#[test]
fn genuinely_huge_value_saturates() {
    let v = BigDecimal::from_str(&format!("1{}", "0".repeat(30))).unwrap();
    assert_eq!(q_from_bigdecimal(&v), Q::PosSat);
    let v = BigDecimal::from_str(&format!("-1{}", "0".repeat(30))).unwrap();
    assert_eq!(q_from_bigdecimal(&v), Q::NegSat);
}

#[test]
fn from_and_try_from_impls_match_named_functions() {
    let v = BigDecimal::from_str("2.71828").unwrap();
    assert_eq!(Q::from(v.clone()), q_from_bigdecimal(&v));
    assert_eq!(
        Exact::try_from(v.clone()).unwrap(),
        exact_from_bigdecimal(&v).unwrap()
    );
}
