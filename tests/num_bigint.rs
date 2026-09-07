//! The `num-bigint` boundary (issue #33 follow-up): a bare `BigInt` as
//! `n / 1`, built on the shared `from_ratio128_dir`/`from_ratio128_exact`
//! core. Unlike a fraction, an integer's own magnitude *is* the value, so
//! "does not fit `i128`" always means genuine saturation, never a resolution
//! limit — no `to_f64` fallback is needed here.

#![cfg(feature = "num-bigint")]

use num_bigint::BigInt;
use the_q::{Dir, Exact, ExactError, Q, Rat, exact_from_bigint, from_bigint_dir, q_from_bigint};

#[test]
fn small_value_is_exact() {
    let v = BigInt::from(42);
    assert_eq!(
        from_bigint_dir(&v, Dir::Nearest).unwrap(),
        Rat::new(42, 1).unwrap()
    );
}

#[test]
fn negative_value_is_exact() {
    let v = BigInt::from(-42);
    assert_eq!(
        from_bigint_dir(&v, Dir::Nearest).unwrap(),
        Rat::new(-42, 1).unwrap()
    );
}

#[test]
fn zero_is_zero() {
    assert_eq!(
        from_bigint_dir(&BigInt::from(0), Dir::Nearest).unwrap(),
        Rat::zero()
    );
}

#[test]
fn value_beyond_i128_is_none_and_saturates_by_sign() {
    let huge = BigInt::from(10).pow(40);
    assert_eq!(from_bigint_dir(&huge, Dir::Nearest), None);
    assert_eq!(q_from_bigint(&huge), Q::PosSat);
    assert_eq!(q_from_bigint(&(-&huge)), Q::NegSat);
    assert_eq!(exact_from_bigint(&huge), Err(ExactError::Inexact));
}

#[test]
fn value_beyond_max_mag_but_within_i128_saturates_too() {
    // Fits an i128 easily, but its magnitude alone exceeds MAX_MAG
    // (2^62 - 1): this is still the "too big" case, not a resolution one.
    let v = BigInt::from(10).pow(30);
    assert_eq!(q_from_bigint(&v), Q::PosSat);
    assert_eq!(exact_from_bigint(&v), Err(ExactError::Inexact));
}

#[test]
fn from_and_try_from_impls_match_named_functions() {
    let v = BigInt::from(123456);
    assert_eq!(Q::from(v.clone()), q_from_bigint(&v));
    assert_eq!(
        Exact::try_from(v.clone()).unwrap(),
        exact_from_bigint(&v).unwrap()
    );
}
