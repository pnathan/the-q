use the_q::{Exact, ExactError, MAX_MAG, Rat};

fn rat(num: i64, den: i64) -> Rat {
    Rat::new(num, den).expect("valid test rational")
}

fn exact(num: i64, den: i64) -> Exact {
    Exact::new(rat(num, den))
}

#[test]
fn add_within_budget_succeeds_exactly() {
    let r = Exact::add(exact(1, 2), exact(1, 2)).expect("1/2 + 1/2 is exact");
    assert_eq!(r.value(), rat(1, 1));
}

#[test]
fn mul_within_budget_succeeds_exactly() {
    let r = Exact::mul(exact(2, 1), exact(3, 1)).expect("2 * 3 is exact");
    assert_eq!(r.value(), rat(6, 1));
}

#[test]
fn sub_within_budget_succeeds_exactly() {
    let r = Exact::sub(exact(3, 4), exact(1, 4)).expect("3/4 - 1/4 is exact");
    assert_eq!(r.value(), rat(1, 2));
}

#[test]
fn div_within_budget_succeeds_exactly() {
    let r = Exact::div(exact(1, 2), exact(1, 3)).expect("(1/2) / (1/3) is exact");
    assert_eq!(r.value(), rat(3, 2));
}

#[test]
fn add_forced_to_saturate_is_inexact() {
    let big = Exact::new(Rat::new(MAX_MAG, 1).unwrap());
    assert_eq!(Exact::add(big, big), Err(ExactError::Inexact));
}

#[test]
fn add_with_large_coprime_denominators_needs_rounding_and_is_inexact() {
    // 1/3037000493 + 1/3037000499 reduces to a denominator of about 9.2e18,
    // well past MAX_MAG (about 4.6e18); the sum is tiny, so this is not
    // saturation, just a genuine dyadic-snap case.
    let a = exact(1, 3_037_000_493);
    let b = exact(1, 3_037_000_499);
    assert_eq!(Exact::add(a, b), Err(ExactError::Inexact));
}

#[test]
fn div_by_zero_is_division_by_zero_not_inexact() {
    assert_eq!(
        Exact::div(exact(1, 2), exact(0, 1)),
        Err(ExactError::DivisionByZero)
    );
}

#[test]
fn add_associativity_holds_when_both_orders_succeed() {
    let (a, b, c) = (exact(1, 2), exact(1, 3), exact(1, 6));
    let ab = Exact::add(a, b).unwrap();
    let bc = Exact::add(b, c).unwrap();
    let left = Exact::add(ab, c).unwrap();
    let right = Exact::add(a, bc).unwrap();
    assert_eq!(left.value(), right.value());
}

#[test]
fn mul_associativity_holds_when_both_orders_succeed() {
    let (a, b, c) = (exact(1, 2), exact(2, 3), exact(3, 4));
    let ab = Exact::mul(a, b).unwrap();
    let bc = Exact::mul(b, c).unwrap();
    let left = Exact::mul(ab, c).unwrap();
    let right = Exact::mul(a, bc).unwrap();
    assert_eq!(left.value(), right.value());
}

#[test]
fn distributivity_holds_when_every_step_succeeds() {
    let (a, b, c) = (exact(1, 2), exact(1, 3), exact(1, 6));
    let bc = Exact::add(b, c).unwrap();
    let lhs = Exact::mul(a, bc).unwrap();
    let ab = Exact::mul(a, b).unwrap();
    let ac = Exact::mul(a, c).unwrap();
    let rhs = Exact::add(ab, ac).unwrap();
    assert_eq!(lhs.value(), rhs.value());
}

#[test]
fn checked_and_result_apis_agree() {
    assert_eq!(
        Exact::checked_add(exact(1, 2), exact(1, 2)).map(|e| e.value()),
        Some(rat(1, 1))
    );
    assert!(Exact::checked_div(exact(1, 2), exact(0, 1)).is_none());
}
