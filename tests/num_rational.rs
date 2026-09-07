//! The `num-rational` boundary (issue #33 follow-up): `Ratio<i64>` (always
//! exact) and `BigRational` (arbitrary precision, needs a fallible `i128`
//! extraction first), both built on the shared `from_ratio128_dir`/
//! `from_ratio128_exact` core.

#![cfg(feature = "num-rational")]

use num_bigint::BigInt;
use num_rational::{BigRational, Ratio};
use the_q::{
    Dir, Exact, ExactError, Q, Rat, exact_from_big_rational, exact_from_num_rational_i64,
    from_big_rational_dir, from_big_rational_exact, from_num_rational_i64_dir, q_from_big_rational,
    q_from_num_rational_i64,
};

#[test]
fn ratio_i64_is_exact() {
    let v = Ratio::new(3i64, 4);
    assert_eq!(
        from_num_rational_i64_dir(v, Dir::Nearest),
        Rat::new(3, 4).unwrap()
    );
}

#[test]
fn ratio_i64_reduces_like_rat_does() {
    let v = Ratio::new(2i64, 4); // num-rational reduces this to 1/2 itself
    assert_eq!(
        from_num_rational_i64_dir(v, Dir::Nearest),
        Rat::new(1, 2).unwrap()
    );
}

#[test]
fn ratio_i64_from_impl_matches_the_named_function() {
    let v = Ratio::new(-7i64, 3);
    assert_eq!(Q::from(v), q_from_num_rational_i64(v));
}

#[test]
fn ratio_i64_exact_try_from_matches_the_named_function() {
    let v = Ratio::new(5i64, 8);
    assert_eq!(
        Exact::try_from(v).unwrap(),
        exact_from_num_rational_i64(v).unwrap()
    );
    assert_eq!(
        exact_from_num_rational_i64(v).unwrap(),
        Exact::new(Rat::new(5, 8).unwrap())
    );
}

#[test]
fn big_rational_small_value_is_exact() {
    let v = BigRational::new(BigInt::from(22), BigInt::from(7));
    let r = from_big_rational_dir(&v, Dir::Nearest).unwrap();
    assert_eq!(r, Rat::new(22, 7).unwrap());
    assert_eq!(from_big_rational_exact(&v).unwrap(), r);
}

#[test]
fn big_rational_too_wide_for_i128_is_none_but_q_falls_back_to_f64() {
    // Both terms exceed i128, but the value itself (~1) does not exceed the
    // budget: `from_big_rational_dir`/`exact` refuse (arbitrary precision is
    // not representable exactly), but `q_from_big_rational` still produces a
    // real number via its `to_f64` fallback, not a saturation.
    let huge_denom = BigInt::from(10).pow(40);
    let huge_numer = &huge_denom + BigInt::from(1);
    let v = BigRational::new(huge_numer, huge_denom);
    assert_eq!(from_big_rational_dir(&v, Dir::Nearest), None);
    assert_eq!(from_big_rational_exact(&v), None);
    assert_eq!(exact_from_big_rational(&v), Err(ExactError::Inexact));
    match q_from_big_rational(&v) {
        Q::Number(r) => {
            // The value is ~1 + 1e-40, indistinguishable from 1 at f64
            // precision, let alone this crate's grid.
            assert_eq!(r, Rat::one());
        }
        other => panic!("expected a number close to 1, got {other}"),
    }
}

#[test]
fn big_rational_genuinely_huge_saturates() {
    let v = BigRational::new(BigInt::from(10).pow(30), BigInt::from(1));
    assert_eq!(q_from_big_rational(&v), Q::PosSat);
    let v = BigRational::new(-BigInt::from(10).pow(30), BigInt::from(1));
    assert_eq!(q_from_big_rational(&v), Q::NegSat);
}

#[test]
fn big_rational_from_and_try_from_impls_match_named_functions() {
    let v = BigRational::new(BigInt::from(3), BigInt::from(4));
    assert_eq!(Q::from(v.clone()), q_from_big_rational(&v));
    assert_eq!(
        Exact::try_from(v.clone()).unwrap(),
        exact_from_big_rational(&v).unwrap()
    );
}
