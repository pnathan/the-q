//! Property tests (spec §7): invariants, algebraic laws, determinism,
//! monotonicity, round-trip.

mod common;

use proptest::prelude::*;
use the_q::{Dir, Q};

fn any_i64_in_budget() -> impl Strategy<Value = i64> {
    -(the_q::MAX_MAGNITUDE)..=the_q::MAX_MAGNITUDE
}

fn wide_q() -> impl Strategy<Value = Q> {
    (any_i64_in_budget(), 1i64..=the_q::MAX_MAGNITUDE).prop_map(|(n, d)| Q::new(n, d).unwrap())
}

fn small_q() -> impl Strategy<Value = Q> {
    (-1_000_000i64..=1_000_000, 1i64..=1_000_000).prop_map(|(n, d)| Q::new(n, d).unwrap())
}

fn assert_canonical(q: Q) {
    assert!(q.denominator() > 0, "I1: den must be > 0, got {q}");
    assert!(
        q.numerator().unsigned_abs() <= the_q::MAX_MAGNITUDE as u64,
        "I2: |num| out of budget in {q}"
    );
    assert!(
        q.denominator() <= the_q::MAX_MAGNITUDE,
        "I2: den out of budget in {q}"
    );
    if q.numerator() == 0 {
        assert_eq!(q.denominator(), 1, "I1: zero must have den == 1, got {q}");
    }
    fn gcd(mut a: u64, mut b: u64) -> u64 {
        while b != 0 {
            (a, b) = (b, a % b);
        }
        a
    }
    assert_eq!(
        gcd(q.numerator().unsigned_abs(), q.denominator().unsigned_abs()),
        1,
        "I1: not in lowest terms: {q}"
    );
}

proptest! {
    // --- V1: invariant preserved by every op ---

    #[test]
    fn invariants_after_add(a in wide_q(), b in wide_q()) {
        assert_canonical(the_q::add(a, b));
    }

    #[test]
    fn invariants_after_sub(a in wide_q(), b in wide_q()) {
        assert_canonical(the_q::sub(a, b));
    }

    #[test]
    fn invariants_after_mul(a in wide_q(), b in wide_q()) {
        assert_canonical(the_q::mul(a, b));
    }

    #[test]
    fn invariants_after_div(a in wide_q(), b in wide_q().prop_filter("nonzero", |q| !q.is_zero())) {
        assert_canonical(the_q::div(a, b));
    }

    #[test]
    fn invariants_after_neg_abs_recip(a in wide_q().prop_filter("nonzero", |q| !q.is_zero())) {
        assert_canonical(the_q::neg(a));
        assert_canonical(the_q::abs(a));
        assert_canonical(the_q::recip(a));
    }

    // --- V6: commutativity always holds, even when rounded ---

    #[test]
    fn add_commutative(a in wide_q(), b in wide_q()) {
        prop_assert_eq!(the_q::add(a, b), the_q::add(b, a));
    }

    #[test]
    fn mul_commutative(a in wide_q(), b in wide_q()) {
        prop_assert_eq!(the_q::mul(a, b), the_q::mul(b, a));
    }

    // --- V6: associativity/distributivity hold only on the exact path ---

    #[test]
    fn add_associative_when_exact(a in small_q(), b in small_q(), c in small_q()) {
        prop_assert_eq!(
            the_q::add(the_q::add(a, b), c),
            the_q::add(a, the_q::add(b, c))
        );
    }

    #[test]
    fn mul_distributes_over_add_when_exact(a in small_q(), b in small_q(), c in small_q()) {
        prop_assert_eq!(
            the_q::mul(a, the_q::add(b, c)),
            the_q::add(the_q::mul(a, b), the_q::mul(a, c))
        );
    }

    // --- V6: involutions ---

    #[test]
    fn neg_is_involution(a in wide_q()) {
        prop_assert_eq!(the_q::neg(the_q::neg(a)), a);
    }

    #[test]
    fn recip_is_involution(a in wide_q().prop_filter("nonzero", |q| !q.is_zero())) {
        prop_assert_eq!(the_q::recip(the_q::recip(a)), a);
    }

    #[test]
    fn abs_idempotent(a in wide_q()) {
        prop_assert_eq!(the_q::abs(the_q::abs(a)), the_q::abs(a));
    }

    // --- V6: Ord is a total order agreeing with the ghost order (cross-multiplication) ---

    #[test]
    fn ord_agrees_with_cross_multiplication(a in wide_q(), b in wide_q()) {
        let expected = (a.numerator() as i128 * b.denominator() as i128)
            .cmp(&(b.numerator() as i128 * a.denominator() as i128));
        prop_assert_eq!(a.cmp(&b), expected);
    }

    #[test]
    fn ord_is_antisymmetric_and_reflexive(a in wide_q(), b in wide_q()) {
        prop_assert_eq!(a.cmp(&a), std::cmp::Ordering::Equal);
        if a.cmp(&b) == std::cmp::Ordering::Less {
            prop_assert_eq!(b.cmp(&a), std::cmp::Ordering::Greater);
        }
    }

    // --- R4: monotone, exercised in the forced-rounding regime. Two
    // large, near-budget, distinct-parity denominators make `base + lo` and
    // `base + hi` both round (their product denominator vastly exceeds the
    // I2 budget), so this is testing round_to_budget's monotonicity, not
    // just the exact path. ---

    #[test]
    fn add_is_monotone_when_rounded(
        base in wide_q(),
        d1 in (the_q::MAX_MAGNITUDE / 2)..the_q::MAX_MAGNITUDE,
        gap in 1i64..1_000_000,
        delta in 0i64..1_000_000,
    ) {
        let d1 = d1 | 1;
        let d2 = (d1 + gap * 2 + 1) | 1;
        let lo = Q::new(1, d1).unwrap();
        let hi = the_q::add(lo, Q::new(delta, d2).unwrap());
        prop_assert!(hi >= lo);
        prop_assert!(the_q::add(base, lo) <= the_q::add(base, hi));
    }

    // --- from_f64_dir: R2 directedness and R4 monotonicity ---

    #[test]
    fn from_f64_dir_down_le_up(v in -1.0e15f64..1.0e15) {
        prop_assert!(v.is_finite());
        let down = the_q::from_f64_dir(v, Dir::Down);
        let up = the_q::from_f64_dir(v, Dir::Up);
        if let (Some(down), Some(up)) = (down, up) {
            prop_assert!(down <= up);
        }
    }

    #[test]
    fn from_f64_dir_monotone(a in -1.0e15f64..1.0e15, gap in 0.0f64..1.0e15) {
        let b = a + gap; // constructed ordered, rather than filtering random pairs
        for dir in [Dir::Down, Dir::Up, Dir::Nearest] {
            if let (Some(qa), Some(qb)) = (the_q::from_f64_dir(a, dir), the_q::from_f64_dir(b, dir)) {
                prop_assert!(qa <= qb, "monotonicity violated for dir {:?}: {a} -> {qa}, {b} -> {qb}", dir);
            }
        }
    }

    // --- determinism: repeated evaluation is byte-identical ---

    #[test]
    fn deterministic(a in wide_q(), b in wide_q()) {
        prop_assert_eq!(the_q::add(a, b), the_q::add(a, b));
        prop_assert_eq!(the_q::mul(a, b), the_q::mul(a, b));
    }

    // --- in_unit_interval ---

    #[test]
    fn in_unit_interval_matches_definition(a in wide_q()) {
        let expected = a >= Q::zero() && a <= Q::one();
        prop_assert_eq!(a.in_unit_interval(), expected);
    }

    // --- min/max/clamp ---

    #[test]
    fn min_max_clamp(a in wide_q(), b in wide_q(), c in wide_q()) {
        let (lo, hi) = if b <= c { (b, c) } else { (c, b) };
        let clamped = the_q::clamp(a, lo, hi);
        prop_assert!(clamped >= lo && clamped <= hi);
        prop_assert_eq!(the_q::min(a, b), if a <= b { a } else { b });
        prop_assert_eq!(the_q::max(a, b), if a >= b { a } else { b });
    }

    // --- from_decimal is always exact (R1) for realistic decimal places ---

    #[test]
    fn from_decimal_is_exact(mantissa in -1_000_000_000i64..1_000_000_000, dec_places in 0u8..=9) {
        let q = Q::from_decimal(mantissa, dec_places).unwrap();
        let expected_den = 10i128.pow(dec_places as u32);
        let expected = malachite_q::Rational::from_signeds::<i128>(mantissa as i128, expected_den);
        prop_assert_eq!(common::q_to_rational(q), expected);
    }
}

#[cfg(feature = "serde")]
proptest! {
    #[test]
    fn serde_roundtrip_is_exact(a in wide_q()) {
        let json = serde_json::to_string(&a).unwrap();
        let back: Q = serde_json::from_str(&json).unwrap();
        prop_assert_eq!(back, a);
    }
}

#[cfg(feature = "serde")]
#[test]
fn serde_deserialize_canonicalizes_non_canonical_wire_form() {
    // (2, 4) is a valid but non-canonical wire form -- must still decode
    // safely, to the canonical 1/2, not be rejected.
    let back: Q = serde_json::from_str("[2, 4]").unwrap();
    assert_eq!(back, Q::new(1, 2).unwrap());
}

#[cfg(feature = "serde")]
#[test]
fn serde_deserialize_rejects_zero_denominator() {
    let result: Result<Q, _> = serde_json::from_str("[1, 0]");
    assert!(result.is_err());
}
