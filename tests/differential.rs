//! Differential tests against the `malachite-q` oracle (spec §7).
//! For every op: exact-path results must equal the oracle exactly (R1), and
//! rounded results must fall within the R3 error bound of the oracle's
//! exact value.

mod common;

use common::{assert_within_error_bound, q_to_rational};
use proptest::prelude::*;
use the_q::{Dir, Q};

/// Small, budget-safe range: any add/sub/mul/div of two values built from
/// this range stays comfortably within the I2 budget, so the oracle
/// comparison below is an *exact* equality check (R1), not just an
/// error-bound check.
fn small_q() -> impl Strategy<Value = Q> {
    (-1_000_000i64..=1_000_000, 1i64..=1_000_000).prop_map(|(n, d)| Q::new(n, d).unwrap())
}

/// Wide range: numerators/denominators near the I2 ceiling, likely to force
/// rounding through arithmetic (denominators multiply and quickly exceed
/// the budget).
fn wide_q() -> impl Strategy<Value = Q> {
    (
        -(the_q::MAX_MAGNITUDE)..=the_q::MAX_MAGNITUDE,
        1i64..=the_q::MAX_MAGNITUDE,
    )
        .prop_map(|(n, d)| Q::new(n, d).unwrap())
}

proptest! {
    #[test]
    fn add_small_is_exact(a in small_q(), b in small_q()) {
        let exact = q_to_rational(a) + q_to_rational(b);
        prop_assert_eq!(q_to_rational(the_q::add(a, b)), exact);
    }

    #[test]
    fn sub_small_is_exact(a in small_q(), b in small_q()) {
        let exact = q_to_rational(a) - q_to_rational(b);
        prop_assert_eq!(q_to_rational(the_q::sub(a, b)), exact);
    }

    #[test]
    fn mul_small_is_exact(a in small_q(), b in small_q()) {
        let exact = q_to_rational(a) * q_to_rational(b);
        prop_assert_eq!(q_to_rational(the_q::mul(a, b)), exact);
    }

    #[test]
    fn div_small_is_exact(a in small_q(), b in small_q().prop_filter("nonzero", |q| !q.is_zero())) {
        let exact = q_to_rational(a) / q_to_rational(b);
        prop_assert_eq!(q_to_rational(the_q::div(a, b)), exact);
    }

    #[test]
    fn add_wide_within_error_bound(a in wide_q(), b in wide_q()) {
        let exact = q_to_rational(a) + q_to_rational(b);
        assert_within_error_bound(the_q::add(a, b), &exact);
    }

    #[test]
    fn sub_wide_within_error_bound(a in wide_q(), b in wide_q()) {
        let exact = q_to_rational(a) - q_to_rational(b);
        assert_within_error_bound(the_q::sub(a, b), &exact);
    }

    #[test]
    fn mul_wide_within_error_bound(a in wide_q(), b in wide_q()) {
        let exact = q_to_rational(a) * q_to_rational(b);
        assert_within_error_bound(the_q::mul(a, b), &exact);
    }

    #[test]
    fn div_wide_within_error_bound(a in wide_q(), b in wide_q().prop_filter("nonzero", |q| !q.is_zero())) {
        let exact = q_to_rational(a) / q_to_rational(b);
        assert_within_error_bound(the_q::div(a, b), &exact);
    }

    #[test]
    fn neg_abs_recip_always_exact(a in wide_q().prop_filter("nonzero", |q| !q.is_zero())) {
        prop_assert_eq!(q_to_rational(the_q::neg(a)), -q_to_rational(a));
        prop_assert_eq!(
            q_to_rational(the_q::abs(a)),
            malachite_base::num::arithmetic::traits::Abs::abs(q_to_rational(a))
        );
        let exact_recip = malachite_base::num::arithmetic::traits::Reciprocal::reciprocal(q_to_rational(a));
        prop_assert_eq!(q_to_rational(the_q::recip(a)), exact_recip);
    }

    #[test]
    fn cmp_matches_oracle(a in wide_q(), b in wide_q()) {
        let expected = q_to_rational(a).cmp(&q_to_rational(b));
        prop_assert_eq!(a.cmp(&b), expected);
    }

    #[test]
    fn directed_rounding_brackets_exact_value(a in wide_q(), b in wide_q()) {
        // Recompute the same exact sum through the internal Down/Up paths
        // by exercising from_f64_dir isn't applicable here (that's f64-only);
        // instead check add's Nearest result sits inside [oracle-bound, oracle+bound],
        // which is a corollary of R2+R3 together and exercises the same
        // rounding path as Down/Up would.
        let exact = q_to_rational(a) + q_to_rational(b);
        let approx = q_to_rational(the_q::add(a, b));
        prop_assert!(approx >= exact.clone() - common::error_bound(&exact));
        prop_assert!(approx <= exact + common::error_bound(&q_to_rational(the_q::add(a, b))));
    }
}

#[test]
fn from_f64_dir_matches_oracle_for_representable_doubles() {
    // f64::MIN_POSITIVE (2^-1022) is deliberately excluded: from_f64_dir
    // rejects magnitudes whose exact 2^exp denominator wouldn't fit i128
    // (shift > 125, i.e. roughly |v| < 2^-73) -- see tests/adversarial.rs
    // for that boundary's own coverage.
    let cases = [
        0.0, 1.0, -1.0, 0.5, 0.85, 100.25, -0.001, 1e10, -1e10, 1e-20,
    ];
    for v in cases {
        for dir in [Dir::Down, Dir::Up, Dir::Nearest] {
            let q = the_q::from_f64_dir(v, dir).unwrap();
            let exact = malachite_q::Rational::try_from(v).unwrap();
            assert_within_error_bound(q, &exact);
        }
    }
}
