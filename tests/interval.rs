//! Tests for `QI`, the directed-rounding interval type (spec M6, stretch).
//! The core property under test: every op's result interval is a *sound
//! enclosure* of the exact mathematical result -- checked against the
//! `malachite-q` oracle, the same discipline as `tests/differential.rs`.

mod common;

use common::q_to_rational;
use proptest::prelude::*;
use the_q::{interval_ops, Q, QI};

fn wide_q() -> impl Strategy<Value = Q> {
    (
        -(the_q::MAX_MAGNITUDE)..=the_q::MAX_MAGNITUDE,
        1i64..=the_q::MAX_MAGNITUDE,
    )
        .prop_map(|(n, d)| Q::new(n, d).unwrap())
}

fn wide_qi() -> impl Strategy<Value = QI> {
    (wide_q(), wide_q()).prop_map(|(a, b)| {
        if a <= b {
            QI::new(a, b).unwrap()
        } else {
            QI::new(b, a).unwrap()
        }
    })
}

fn assert_encloses(qi: QI, exact: &malachite_q::Rational) {
    let lo = q_to_rational(qi.lo());
    let hi = q_to_rational(qi.hi());
    assert!(
        lo <= *exact && *exact <= hi,
        "interval [{lo}, {hi}] does not enclose exact value {exact}"
    );
}

#[test]
fn new_rejects_lo_gt_hi() {
    assert!(QI::new(Q::one(), Q::zero()).is_none());
    assert!(QI::new(Q::zero(), Q::one()).is_some());
    assert!(QI::new(Q::zero(), Q::zero()).is_some());
}

#[test]
fn point_contains_only_itself_among_endpoints() {
    let q = Q::new(3, 7).unwrap();
    let p = QI::point(q);
    assert_eq!(p.lo(), q);
    assert_eq!(p.hi(), q);
    assert!(p.contains(q));
}

#[test]
fn div_none_when_divisor_contains_zero() {
    let a = QI::point(Q::one());
    let straddles = QI::new(Q::new(-1, 2).unwrap(), Q::new(1, 2).unwrap()).unwrap();
    let touches = QI::new(Q::zero(), Q::one()).unwrap();
    assert!(interval_ops::div(a, straddles).is_none());
    assert!(interval_ops::div(a, touches).is_none());

    let positive = QI::new(Q::new(1, 4).unwrap(), Q::one()).unwrap();
    assert!(interval_ops::div(a, positive).is_some());
}

proptest! {
    #[test]
    fn contains_matches_definition(qi in wide_qi(), q in wide_q()) {
        prop_assert_eq!(qi.contains(q), qi.lo() <= q && q <= qi.hi());
    }

    #[test]
    fn add_encloses_every_pointwise_sum(a in wide_qi(), b in wide_qi()) {
        let result = interval_ops::add(a, b);
        prop_assert!(result.lo() <= result.hi());
        for &qa in &[a.lo(), a.hi()] {
            for &qb in &[b.lo(), b.hi()] {
                let exact = q_to_rational(qa) + q_to_rational(qb);
                assert_encloses(result, &exact);
            }
        }
    }

    #[test]
    fn sub_encloses_every_pointwise_difference(a in wide_qi(), b in wide_qi()) {
        let result = interval_ops::sub(a, b);
        prop_assert!(result.lo() <= result.hi());
        for &qa in &[a.lo(), a.hi()] {
            for &qb in &[b.lo(), b.hi()] {
                let exact = q_to_rational(qa) - q_to_rational(qb);
                assert_encloses(result, &exact);
            }
        }
    }

    #[test]
    fn mul_encloses_every_corner_product(a in wide_qi(), b in wide_qi()) {
        let result = interval_ops::mul(a, b);
        prop_assert!(result.lo() <= result.hi());
        for &qa in &[a.lo(), a.hi()] {
            for &qb in &[b.lo(), b.hi()] {
                let exact = q_to_rational(qa) * q_to_rational(qb);
                assert_encloses(result, &exact);
            }
        }
    }

    #[test]
    fn neg_encloses_negation(a in wide_qi()) {
        let result = interval_ops::neg(a);
        prop_assert!(result.lo() <= result.hi());
        assert_encloses(result, &(-q_to_rational(a.lo())));
        assert_encloses(result, &(-q_to_rational(a.hi())));
    }

    #[test]
    fn div_encloses_every_corner_quotient(
        a in wide_qi(),
        b in wide_q().prop_filter("positive", |q| *q > Q::zero()),
        gap in 0i64..1_000_000,
    ) {
        // Construct b's interval strictly positive (b, b+gap]-ish) so it
        // never contains zero, keeping this property test's div() calls
        // always Some.
        let b_hi = the_q::add(b, Q::new(gap, 1).unwrap());
        let bi = QI::new(b, b_hi).unwrap();
        let result = interval_ops::div(a, bi).expect("strictly positive divisor");
        prop_assert!(result.lo() <= result.hi());
        for &qa in &[a.lo(), a.hi()] {
            for &qb in &[bi.lo(), bi.hi()] {
                let exact = q_to_rational(qa) / q_to_rational(qb);
                assert_encloses(result, &exact);
            }
        }
    }

    #[test]
    fn width_is_hi_minus_lo(a in wide_qi()) {
        prop_assert_eq!(a.width(), the_q::sub(a.hi(), a.lo()));
    }

    #[test]
    fn from_f64_encloses_the_input(v in -1.0e15f64..1.0e15) {
        if let Some(qi) = QI::from_f64(v) {
            prop_assert!(qi.lo() <= qi.hi());
            let exact = malachite_q::Rational::try_from(v).unwrap();
            assert_encloses(qi, &exact);
        }
    }
}
