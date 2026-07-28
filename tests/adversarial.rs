//! Adversarial fixtures (spec §7): budget-edge values, sign edges,
//! `i64::MIN` exclusion, long fold chains, magnitude-ceiling saturation.

mod common;

use common::{assert_within_error_bound, q_to_rational};
use the_q::{Dir, Q};

const MAX: i64 = the_q::MAX_MAGNITUDE;

#[test]
fn budget_edge_values_round_trip() {
    let q = Q::new(MAX, MAX).unwrap(); // reduces to 1/1
    assert_eq!(q, Q::one());

    let q = Q::new(MAX, 1).unwrap();
    assert_eq!(q.numerator(), MAX);
    assert_eq!(q.denominator(), 1);

    let q = Q::new(-MAX, 1).unwrap();
    assert_eq!(q.numerator(), -MAX);

    let q = Q::new(1, MAX).unwrap();
    assert_eq!(q.denominator(), MAX);
}

#[test]
fn budget_edge_values_reject_out_of_range() {
    assert!(Q::new(MAX + 1, 1).is_none());
    assert!(Q::new(1, MAX + 1).is_none());
    assert!(Q::from_int(MAX + 1).is_none());
    assert!(Q::from_int(-(MAX + 1)).is_none());
    assert!(Q::from_int(MAX).is_some());
    assert!(Q::from_int(-MAX).is_some());
}

#[test]
fn sign_edges() {
    assert_eq!(Q::new(1, -1).unwrap(), Q::new(-1, 1).unwrap());
    assert_eq!(Q::new(-1, -1).unwrap(), Q::one());
    assert_eq!(the_q::neg(Q::zero()), Q::zero());
    assert_eq!(the_q::abs(Q::new(-3, 4).unwrap()), Q::new(3, 4).unwrap());
    assert_eq!(Q::zero().signum(), 0);
    assert_eq!(Q::one().signum(), 1);
    assert_eq!(Q::new(-1, 2).unwrap().signum(), -1);
}

/// `I2` excludes `i64::MIN` (`|i64::MIN| == 2^63`, overflowing the budget
/// entirely); `Q::new`/`from_int` must reject it, not panic.
/// `i64::MIN.unsigned_abs()` itself is well-defined (`2^63` fits `u64`), so
/// this is a rejection test, not a panic-avoidance test.
#[test]
fn i64_min_is_rejected_not_panicking() {
    assert!(Q::new(i64::MIN, 1).is_none());
    assert!(Q::from_int(i64::MIN).is_none());
    assert!(Q::new(1, i64::MIN).is_none()); // den < 0 path negates i64::MIN
}

#[test]
fn zero_constructors_are_canonical() {
    assert_eq!(Q::new(0, 5).unwrap(), Q::zero());
    assert_eq!(Q::new(0, -5).unwrap(), Q::zero());
    assert_eq!(Q::zero().denominator(), 1);
}

#[test]
fn div_by_zero_panics() {
    let result = std::panic::catch_unwind(|| the_q::div(Q::one(), Q::zero()));
    assert!(
        result.is_err(),
        "div by zero must panic (precondition violation), not return a bad Q"
    );
}

#[test]
fn recip_of_zero_panics() {
    let result = std::panic::catch_unwind(|| the_q::recip(Q::zero()));
    assert!(result.is_err());
}

#[test]
fn clamp_with_lo_gt_hi_panics() {
    let result = std::panic::catch_unwind(|| the_q::clamp(Q::zero(), Q::one(), Q::zero()));
    assert!(result.is_err());
}

/// Magnitude-ceiling saturation (rounding.rs module docs): the product of
/// two near-max-magnitude values exceeds anything representable, even
/// approximately. Must saturate, not panic or silently wrap.
#[test]
fn magnitude_ceiling_saturates_instead_of_panicking() {
    let big = Q::new(MAX, 1).unwrap();
    let result = the_q::mul(big, big);
    assert_eq!(result.numerator(), MAX);
    assert_eq!(result.denominator(), 1);

    let neg_big = the_q::neg(big);
    let result = the_q::mul(big, neg_big);
    assert_eq!(result.numerator(), -MAX);
    assert_eq!(result.denominator(), 1);
}

/// Adding two unit fractions with large, coprime (in fact prime) denominators
/// forces a genuinely out-of-budget exact denominator (product of two
/// ~2^61 primes is ~2^122), exercising the rounding path end to end and
/// checking it against the exact oracle value.
#[test]
fn coprime_large_denominator_add_forces_rounding_within_bound() {
    // Two distinct large primes < 2^62 - 1.
    const P1: i64 = 4_611_686_018_427_387_847; // prime near 2^62
    const P2: i64 = 4_611_686_018_427_387_733; // another prime near 2^62
    let a = Q::new(1, P1).unwrap();
    let b = Q::new(1, P2).unwrap();
    let result = the_q::add(a, b);

    // Confirm this genuinely exercised rounding: the exact denominator
    // P1*P2 vastly exceeds the budget.
    assert!((P1 as i128) * (P2 as i128) > the_q::MAX_MAGNITUDE as i128);

    let exact = q_to_rational(a) + q_to_rational(b);
    assert_within_error_bound(result, &exact);
    assert!(result.denominator() <= the_q::MAX_MAGNITUDE);
}

/// Long fold chain (10^4 ops): accumulated error must stay within
/// `k * 2^-60` of the oracle's exact running value (spec §4 point 2).
#[test]
fn long_fold_chain_error_stays_bounded() {
    use malachite_q::Rational;

    let mut acc = Q::zero();
    let mut exact = Rational::from(0);
    let k = 10_000usize;
    for i in 1..=k {
        let term = Q::new((i % 97) as i64 + 1, (i % 53) as i64 + 1).unwrap();
        acc = the_q::add(acc, term);
        exact += q_to_rational(term);
    }
    let approx = q_to_rational(acc);
    let diff = if approx >= exact {
        approx.clone() - exact.clone()
    } else {
        exact.clone() - approx.clone()
    };
    let one = Rational::from(1);
    let mag = std::cmp::max(exact.clone(), one);
    let bound_per_op = Rational::from_signeds::<i64>(1, 1i64 << 60);
    let bound = mag * bound_per_op * Rational::from(k as u64);
    assert!(
        diff <= bound,
        "accumulated error {diff} exceeds k*2^-60 bound {bound}"
    );
}

#[test]
fn from_f64_dir_rejects_non_finite() {
    assert!(the_q::from_f64_dir(f64::NAN, Dir::Nearest).is_none());
    assert!(the_q::from_f64_dir(f64::INFINITY, Dir::Nearest).is_none());
    assert!(the_q::from_f64_dir(f64::NEG_INFINITY, Dir::Nearest).is_none());
}

#[test]
fn from_f64_dir_zero_and_representable() {
    assert_eq!(the_q::from_f64_dir(0.0, Dir::Nearest), Some(Q::zero()));
    assert_eq!(the_q::from_f64_dir(-0.0, Dir::Nearest), Some(Q::zero()));
    assert_eq!(
        the_q::from_f64_dir(0.5, Dir::Nearest),
        Some(Q::new(1, 2).unwrap())
    );
    assert_eq!(
        the_q::from_f64_dir(2.0, Dir::Nearest),
        Some(Q::new(2, 1).unwrap())
    );
}

/// Values whose exact `mantissa * 2^exp` denominator wouldn't fit `i128`
/// (roughly `|v| < 2^-73`) are rejected outright rather than silently
/// snapped to zero or overflowing -- see `convert::decompose` / `from_f64_dir`.
#[test]
fn from_f64_dir_rejects_ultra_tiny_subnormals() {
    assert!(the_q::from_f64_dir(f64::MIN_POSITIVE, Dir::Nearest).is_none());
    assert!(the_q::from_f64_dir(f64::from_bits(1), Dir::Nearest).is_none()); // smallest subnormal
                                                                             // But a merely-small-but-representable value still works.
    assert!(the_q::from_f64_dir(1e-20, Dir::Nearest).is_some());
}

/// A value whose magnitude exceeds what `Q` can represent (`I2`'s
/// `2^62 - 1` ceiling) must be *rejected*, not silently saturated to a
/// value that's off by many orders of magnitude (which would violate R3,
/// not just be surprising) -- unlike the `rounding` module's
/// magnitude-ceiling saturation for arithmetic-op results, which only
/// ever sees results derived from already-in-range operands.
#[test]
fn from_f64_dir_rejects_out_of_range_magnitude() {
    assert!(the_q::from_f64_dir(1e30, Dir::Nearest).is_none());
    assert!(the_q::from_f64_dir(-1e30, Dir::Nearest).is_none());
    assert!(the_q::from_f64_dir(f64::MAX, Dir::Nearest).is_none());
    // Just inside vs. just outside MAX_MAGNITUDE.
    assert!(the_q::from_f64_dir(4.0e18, Dir::Nearest).is_some());
    assert!(the_q::from_f64_dir(1e19, Dir::Nearest).is_none());
}

#[test]
fn to_f64_never_fed_back_is_documented_boundary() {
    // Smoke test for the trusted `to_f64` boundary (TRUSTED.md): exact
    // values round-trip exactly through f64 when they're f64-representable.
    let q = Q::new(1, 2).unwrap();
    assert_eq!(the_q::to_f64(q), 0.5);
}
