// Verified Rational (ℚ) Arithmetic Core
// Exact-with-verified-rounding rational arithmetic, checked by Verus

pub mod q;
pub mod gcd;
pub mod spec;

pub use q::{Q, Direction};

#[cfg(test)]
mod tests {
    use crate::Q;

    #[test]
    fn test_zero_one() {
        let z = Q::zero();
        let o = Q::one();
        assert_eq!(z.numerator(), 0);
        assert_eq!(z.denominator(), 1);
        assert_eq!(o.numerator(), 1);
        assert_eq!(o.denominator(), 1);
    }
}
