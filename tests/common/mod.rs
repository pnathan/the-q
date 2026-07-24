//! Shared oracle helpers for the differential/property test suites.
//! `malachite-q` is a dev-dependency ONLY -- see the crate README's
//! "Why not malachite-q" section and `scripts/check-no-lgpl3-release-deps.sh`.
//!
//! Not every helper is used by every test binary this module is compiled
//! into, hence the blanket `dead_code` allow.
#![allow(dead_code)]

use malachite_base::num::arithmetic::traits::Abs;
use malachite_q::Rational;
use the_q::Q;

pub fn q_to_rational(q: Q) -> Rational {
    Rational::from_signeds::<i64>(q.numerator(), q.denominator())
}

/// `2^-60 * max(1, |exact|)`, the R3 error bound.
pub fn error_bound(exact: &Rational) -> Rational {
    let one = Rational::from_signeds::<i64>(1, 1);
    let mag = exact.clone().abs();
    let mag = std::cmp::max(mag, one);
    let two_pow_neg_60 = Rational::from_signeds::<i64>(1, 1i64 << 60);
    mag * two_pow_neg_60
}

pub fn abs_diff(a: &Rational, b: &Rational) -> Rational {
    if a >= b {
        a.clone() - b.clone()
    } else {
        b.clone() - a.clone()
    }
}

/// Assert `q`'s value is within the R3 bound of `exact`.
pub fn assert_within_error_bound(q: Q, exact: &Rational) {
    let approx = q_to_rational(q);
    let diff = abs_diff(&approx, exact);
    let bound = error_bound(exact);
    assert!(
        diff <= bound,
        "R3 violated: |{approx} - {exact}| = {diff} > bound {bound}"
    );
}
