//! In-crate unit tests (no external oracle). The heavy differential and
//! property tests live under `tests/`.

use super::*;

fn q(n: i64, d: i64) -> Q {
    Q::new(n, d).unwrap()
}

#[test]
fn constants() {
    assert!(Q::zero().is_zero());
    assert!(Q::one().is_one());
    assert_eq!(Q::zero().numer(), 0);
    assert_eq!(Q::zero().denom(), 1);
}

#[test]
fn canonicalization() {
    // sign moves to numerator, denominator stays positive
    let a = q(1, -2);
    assert_eq!(a.numer(), -1);
    assert_eq!(a.denom(), 2);
    // GCD reduction
    let b = q(6, 8);
    assert_eq!(b.numer(), 3);
    assert_eq!(b.denom(), 4);
    // zero normalizes to 0/1
    let z = q(0, 5);
    assert_eq!(z.numer(), 0);
    assert_eq!(z.denom(), 1);
}

#[test]
fn new_rejects_zero_den() {
    assert!(Q::new(1, 0).is_none());
}

#[test]
fn from_int_budget() {
    assert_eq!(Q::from_int(5).unwrap().numer(), 5);
    assert!(Q::from_int(i64::MIN).is_none());
    assert!(Q::from_int(BUDGET).is_some());
    assert!(Q::from_int(BUDGET + 1).is_none());
}

#[test]
fn from_decimal_examples() {
    assert!(Q::from_decimal(85, 2).unwrap().eq(q(17, 20)));
    assert!(Q::from_decimal(5, 1).unwrap().eq(q(1, 2)));
    assert!(Q::from_decimal(-125, 3).unwrap().eq(q(-1, 8)));
    assert!(Q::from_decimal(0, 4).unwrap().is_zero());
}

#[test]
fn exact_arithmetic_small() {
    assert!(q(1, 2).add(q(1, 3)).eq(q(5, 6)));
    assert!(q(1, 2).sub(q(1, 3)).eq(q(1, 6)));
    assert!(q(2, 3).mul(q(3, 4)).eq(q(1, 2)));
    assert!(q(2, 3).div(q(4, 9)).eq(q(3, 2)));
}

#[test]
fn neg_abs_recip() {
    assert!(q(3, 4).neg().eq(q(-3, 4)));
    assert!(q(-3, 4).abs().eq(q(3, 4)));
    assert!(q(3, 4).recip().eq(q(4, 3)));
    assert!(q(-3, 4).recip().eq(q(-4, 3)));
    // recip involution
    assert!(q(7, 5).recip().recip().eq(q(7, 5)));
}

#[test]
fn ordering_total_and_correct() {
    assert!(q(3, 4).gt(q(5, 7))); // 0.75 > 0.714 — the case where derived Ord would be WRONG
    assert!(q(5, 7).lt(q(3, 4)));
    assert!(q(-1, 2).lt(q(1, 3)));
    let mut v = [q(3, 4), q(5, 7), q(-1, 2), q(1, 1)];
    v.sort();
    assert_eq!(v, [q(-1, 2), q(5, 7), q(3, 4), q(1, 1)]);
}

#[test]
fn predicates() {
    assert!(q(1, 2).in_unit_interval());
    assert!(Q::zero().in_unit_interval());
    assert!(Q::one().in_unit_interval());
    assert!(!q(3, 2).in_unit_interval());
    assert!(!q(-1, 2).in_unit_interval());
    assert_eq!(q(3, 4).signum(), 1);
    assert_eq!(q(-3, 4).signum(), -1);
    assert_eq!(Q::zero().signum(), 0);
}

#[test]
fn min_max_clamp() {
    assert!(q(1, 3).min(q(1, 2)).eq(q(1, 3)));
    assert!(q(1, 3).max(q(1, 2)).eq(q(1, 2)));
    assert!(q(2, 1).clamp(Q::zero(), Q::one()).eq(Q::one()));
    assert!(q(-1, 1).clamp(Q::zero(), Q::one()).eq(Q::zero()));
    assert!(q(1, 2).clamp(Q::zero(), Q::one()).eq(q(1, 2)));
}

#[test]
#[should_panic]
fn div_by_zero_panics() {
    let _ = q(1, 2).div(Q::zero());
}

#[test]
fn checked_div_none_on_zero() {
    assert!(q(1, 2).checked_div(Q::zero()).is_none());
    assert!(q(1, 2).checked_div(q(1, 4)).unwrap().eq(q(2, 1)));
}

#[test]
fn nary_helpers() {
    let xs = [q(1, 2), q(1, 3), q(1, 6)];
    assert!(sum(&xs).eq(Q::one()));
    let ys = [q(2, 1), q(3, 1), q(1, 2)];
    assert!(product(&ys).eq(q(3, 1)));
    let pairs = [(q(1, 1), q(2, 1)), (q(3, 1), q(4, 1))];
    // (1*2 + 3*4)/(1+3) = 14/4 = 7/2
    assert!(weighted_mean(&pairs).unwrap().eq(q(7, 2)));
    assert!(weighted_mean(&[]).is_none());
}

#[test]
fn display() {
    extern crate std;
    assert_eq!(std::format!("{}", q(3, 4)), "3/4");
    assert_eq!(std::format!("{}", q(-1, 2)), "-1/2");
}

#[test]
fn commutativity_exact() {
    let a = q(2, 7);
    let b = q(3, 5);
    assert!(a.add(b).eq(b.add(a)));
    assert!(a.mul(b).eq(b.mul(a)));
}

#[test]
fn from_f64_exact_dyadic() {
    // 0.5, 0.25, 0.75 are exact dyadic rationals — all directions agree.
    for &d in &[Dir::Down, Dir::Up, Dir::Nearest] {
        assert!(Q::from_f64_dir(0.5, d).unwrap().eq(q(1, 2)));
        assert!(Q::from_f64_dir(0.25, d).unwrap().eq(q(1, 4)));
        assert!(Q::from_f64_dir(-0.75, d).unwrap().eq(q(-3, 4)));
        assert!(Q::from_f64_dir(3.0, d).unwrap().eq(q(3, 1)));
    }
    assert!(Q::from_f64_dir(f64::NAN, Dir::Nearest).is_none());
    assert!(Q::from_f64_dir(f64::INFINITY, Dir::Nearest).is_none());
}

#[test]
fn from_f64_directed_brackets() {
    // 0.1 is not dyadic; Down ≤ exact ≤ Up must bracket.
    let lo = Q::from_f64_dir(0.1, Dir::Down).unwrap();
    let hi = Q::from_f64_dir(0.1, Dir::Up).unwrap();
    assert!(lo.le(hi));
    // Both within 2^-60 of each other's neighbourhood (dyadic input fits exactly here).
    assert!(lo.le(Q::from_f64_dir(0.1, Dir::Nearest).unwrap()));
    assert!(Q::from_f64_dir(0.1, Dir::Nearest).unwrap().le(hi));
}

#[test]
fn to_f64_roundish() {
    assert_eq!(q(1, 2).to_f64(), 0.5);
    assert_eq!(q(-3, 4).to_f64(), -0.75);
}

#[test]
fn value_magnitude_saturation_edge() {
    // R3 assumes |exact| ≤ 2^62 − 1 (always true for the engine's value domain:
    // opinions in [0,1], counts ≤ 1e5). BUDGET × BUDGET ≈ 2^124 is *outside* that
    // domain and cannot be represented within I2, so the op saturates to the
    // budget extreme (a documented safety net, not an R3 result). This test pins
    // that behavior so it can never silently change.
    let big = q(BUDGET, 1);
    let sat = big.mul(big);
    assert_eq!(sat.denom(), 1);
    assert_eq!(sat.numer(), BUDGET); // saturated, sign preserved
    let neg = big.neg().mul(big);
    assert_eq!(neg.numer(), -BUDGET);
    // Sums that stay within magnitude 2^62 do NOT saturate — they round exactly
    // as R3 promises (here the result is representable, so it's exact).
    assert!(q(1, 3).add(q(1, 6)).eq(q(1, 2)));
}
