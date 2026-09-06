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
fn sub_with_large_coprime_denominators_needs_rounding_and_is_inexact() {
    // 1/3037000493 - 1/3037000499 reduces to a denominator of about 9.2e18.
    let a = exact(1, 3_037_000_493);
    let b = exact(1, 3_037_000_499);
    assert_eq!(Exact::sub(a, b), Err(ExactError::Inexact));
}

#[test]
fn mul_with_large_coprime_denominators_needs_rounding_and_is_inexact() {
    // (1/3037000493) * (1/3037000499) has a denominator of about 9.2e18; the
    // numerator is 1, so no reduction can bring it back into budget.
    let a = exact(1, 3_037_000_493);
    let b = exact(1, 3_037_000_499);
    assert_eq!(Exact::mul(a, b), Err(ExactError::Inexact));
}

#[test]
fn div_with_large_coprime_denominators_needs_rounding_and_is_inexact() {
    // (1/3037000493) / 3037000499 == 1/(3037000493 * 3037000499), same shape
    // as the multiplication case above.
    let a = exact(1, 3_037_000_493);
    let b = exact(3_037_000_499, 1);
    assert_eq!(Exact::div(a, b), Err(ExactError::Inexact));
}

#[test]
fn div_by_zero_is_division_by_zero_not_inexact() {
    assert_eq!(
        Exact::div(exact(1, 2), exact(0, 1)),
        Err(ExactError::DivisionByZero)
    );
}

#[test]
fn add_split_outcome_one_order_fails_while_the_other_succeeds() {
    // The associativity theorem is one-directional: it says nothing unless
    // *every* intermediate operation succeeds. Here (a+b)+c never gets past
    // its first step, while a+(b+c) succeeds trivially -- that success
    // carries no implication about the other bracketing.
    let a = exact(1, 3_037_000_493);
    let b = exact(1, 3_037_000_499);
    let c = exact(-1, 3_037_000_499);
    assert_eq!(Exact::add(a, b), Err(ExactError::Inexact));
    let bc = Exact::add(b, c).expect("b + c is exact zero");
    assert_eq!(bc.value(), rat(0, 1));
    let right = Exact::add(a, bc).expect("a + 0 is exact");
    assert_eq!(right.value(), a.value());
}

#[test]
fn le_agrees_with_ordinary_rat_comparison() {
    assert!(Exact::le(exact(1, 3), exact(1, 2)));
    assert!(!Exact::le(exact(1, 2), exact(1, 3)));
    assert!(Exact::le(exact(1, 2), exact(1, 2)));
}

#[test]
fn is_nonneg_reports_sign() {
    assert!(exact(0, 1).is_nonneg());
    assert!(exact(1, 2).is_nonneg());
    assert!(!exact(-1, 2).is_nonneg());
}

#[test]
fn add_monotone_when_both_sums_succeed() {
    let (a, b, c) = (exact(1, 3), exact(1, 2), exact(1, 6));
    assert!(Exact::le(a, b));
    let ac = Exact::add(a, c).unwrap();
    let bc = Exact::add(b, c).unwrap();
    assert!(Exact::le(ac, bc));
}

#[test]
fn mul_monotone_nonneg_when_both_products_succeed() {
    let (a, b, c) = (exact(1, 3), exact(1, 2), exact(3, 4));
    assert!(Exact::le(a, b));
    assert!(c.is_nonneg());
    let ac = Exact::mul(a, c).unwrap();
    let bc = Exact::mul(b, c).unwrap();
    assert!(Exact::le(ac, bc));
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
