use malachite_q::Rational;
use the_q::{Rat, nary};

fn rat(num: i64, den: i64) -> Rat {
    Rat::new(num, den).expect("valid test rational")
}

fn oracle(value: Rat) -> Rational {
    Rational::from_signeds(value.numerator() as i128, value.denominator() as i128)
}

#[test]
fn weighted_mean_one_zero_and_one_one_is_half() {
    let pairs = [(rat(1, 1), rat(0, 1)), (rat(1, 1), rat(1, 1))];
    let result = nary::weighted_mean(&pairs).expect("positive total weight");
    assert_eq!(result, rat(1, 2));
    assert_eq!(oracle(result), Rational::from_signeds(1i128, 2i128));
}

#[test]
fn weighted_mean_thirds_is_five_ninths() {
    let pairs = [(rat(1, 3), rat(1, 3)), (rat(2, 3), rat(2, 3))];
    let result = nary::weighted_mean(&pairs).expect("positive total weight");
    assert_eq!(result, rat(5, 9));
    assert_eq!(oracle(result), Rational::from_signeds(5i128, 9i128));
}

#[test]
fn weighted_mean_empty_is_none() {
    assert_eq!(nary::weighted_mean(&[]), None);
}

#[test]
fn weighted_mean_all_zero_weights_is_none() {
    let pairs = [(rat(0, 1), rat(0, 1)), (rat(0, 1), rat(1, 1))];
    assert_eq!(nary::weighted_mean(&pairs), None);
}

#[test]
fn weighted_mean_ten_thousand_equal_weights_is_half() {
    let weight = rat(1, 10_000);
    let pairs: Vec<_> = (0..10_000)
        .map(|i| (weight, rat((i % 2) as i64, 1)))
        .collect();
    let result = nary::weighted_mean(&pairs).expect("positive total weight");
    let exact = Rational::from_signeds(1i128, 2i128);
    let got = oracle(result);
    let error = if got >= exact {
        got - exact.clone()
    } else {
        exact.clone() - got
    };
    let k = pairs.len() as i128;
    let theorem_bound = Rational::from_signeds(8 * k, 1i128 << 61);
    assert_eq!(result, rat(1, 2));
    assert_eq!(error, Rational::from_signeds(0i128, 1i128));
    assert!(error <= theorem_bound);
    // delta = 1: exact sum(w) = 1 and 2*k <= 2^61.
    assert!(2 * k <= 1i128 << 61);
}

// A small executable mirror of the theorem's arithmetic preconditions.  It
// intentionally uses cross multiplication, so the check itself does not
// depend on division or floating-point rounding.
fn theorem_delta_preconditions_hold(
    weights: &[(i128, i128)],
    delta_num: i128,
    delta_den: i128,
) -> bool {
    if delta_num <= 0 || delta_den <= 0 {
        return false;
    }
    let mut sum_num = 0i128;
    let mut sum_den = 1i128;
    for &(num, den) in weights {
        if den <= 0 {
            return false;
        }
        sum_num = sum_num * den + num * sum_den;
        sum_den *= den;
    }
    // Exact weight sum >= delta: delta_num * sum_den <= delta_den * sum_num.
    let sum_bound = delta_num * sum_den <= delta_den * sum_num;
    // theorem_weighted_mean_return_error's half-delta condition.
    let half_delta = 2 * (weights.len() as i128) * delta_den <= delta_num * (1i128 << 61);
    sum_bound && half_delta
}

#[test]
fn weighted_mean_delta_checker_rejects_weight_sum_below_delta() {
    let weights = [(1i128, 3i128), (2, 3)];
    // The exact sum is one, which violates the deliberately false delta = 2
    // lower bound even though the half-delta conditioning inequality holds.
    assert!(2 * (weights.len() as i128) <= 2 * (1i128 << 61));
    assert!(!theorem_delta_preconditions_hold(&weights, 2, 1));
}
