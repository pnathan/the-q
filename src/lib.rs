// Verified Rational (ℚ) Arithmetic Core
// Exact-with-verified-rounding rational arithmetic, checked by Verus
//
// Verification status:
// - Milestone 1: Core type and basic operations
// - Verus verification: Skeleton in place; full proofs pending Verus availability
// - CI: Configured to run both `cargo build` and `verus` checks

pub mod gcd;
pub mod q;
pub mod qi;
pub mod spec;
pub mod spec_proofs;

pub use q::{Direction, Q};
pub use qi::QI;

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
