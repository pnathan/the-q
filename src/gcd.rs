/// Euclidean GCD on u64.
///
/// Verus obligation V5: correctness (gcd divides both, is greatest) +
/// termination (b strictly decreases each iteration).
///
/// # Post-conditions (to be proven in Verus)
/// - result divides a and result divides b
/// - for all d: u64, (d divides a && d divides b) ==> d <= result
/// - if a == 0 && b == 0 then result == 0
pub fn gcd(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        let t = b;
        b = a % b;
        a = t;
    }
    a
}

/// Euclidean GCD on u128, for reducing i128 intermediates.
pub(crate) fn gcd128(mut a: u128, mut b: u128) -> u128 {
    while b != 0 {
        let t = b;
        b = a % b;
        a = t;
    }
    a
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn gcd_basics() {
        assert_eq!(gcd(0, 0), 0);
        assert_eq!(gcd(10, 0), 10);
        assert_eq!(gcd(0, 10), 10);
        assert_eq!(gcd(12, 8), 4);
        assert_eq!(gcd(7, 13), 1);
        assert_eq!(gcd(100, 75), 25);
        assert_eq!(gcd(u64::MAX, 1), 1);
        assert_eq!(gcd(u64::MAX, u64::MAX), u64::MAX);
    }

    #[test]
    fn gcd_commutative() {
        for &(a, b) in &[(3, 7), (12, 18), (100, 250), (0, 5), (1, 1)] {
            assert_eq!(gcd(a, b), gcd(b, a));
        }
    }

    #[test]
    fn gcd128_basics() {
        assert_eq!(gcd128(0, 0), 0);
        assert_eq!(gcd128(12, 8), 4);
        let big = 1u128 << 100;
        assert_eq!(gcd128(big, big), big);
        assert_eq!(gcd128(big, 1), 1);
    }
}
