// Property-based tests for Q
// These tests verify correctness, commutativity, and invariant preservation

use the_q::Q;

#[test]
fn test_add_commutativity() {
    let a = Q::new(3, 7).unwrap();
    let b = Q::new(5, 11).unwrap();
    assert_eq!(a.add(b), b.add(a));
}

#[test]
fn test_mul_commutativity() {
    let a = Q::new(3, 7).unwrap();
    let b = Q::new(5, 11).unwrap();
    assert_eq!(a.mul(b), b.mul(a));
}

#[test]
fn test_add_associativity_exact() {
    // Associativity holds on exact path (R1)
    let a = Q::new(1, 2).unwrap();
    let b = Q::new(1, 3).unwrap();
    let c = Q::new(1, 5).unwrap();

    let lhs = a.add(b).add(c);
    let rhs = a.add(b.add(c));

    // For small rationals within budget, this should be exact
    assert_eq!(lhs.to_f64(), rhs.to_f64());
}

#[test]
fn test_mul_associativity_exact() {
    let a = Q::new(2, 3).unwrap();
    let b = Q::new(3, 5).unwrap();
    let c = Q::new(5, 7).unwrap();

    let lhs = a.mul(b).mul(c);
    let rhs = a.mul(b.mul(c));

    assert_eq!(lhs.to_f64(), rhs.to_f64());
}

#[test]
fn test_identity_add() {
    let a = Q::new(7, 11).unwrap();
    let zero = Q::zero();
    assert_eq!(a.add(zero), a);
    assert_eq!(zero.add(a), a);
}

#[test]
fn test_identity_mul() {
    let a = Q::new(7, 11).unwrap();
    let one = Q::one();
    assert_eq!(a.mul(one), a);
    assert_eq!(one.mul(a), a);
}

#[test]
fn test_inverse_add() {
    let a = Q::new(7, 11).unwrap();
    let neg_a = a.neg();
    let sum = a.add(neg_a);
    assert_eq!(sum, Q::zero());
}

#[test]
fn test_inverse_mul() {
    let a = Q::new(7, 11).unwrap();
    let rec_a = a.recip().unwrap();
    let prod = a.mul(rec_a);
    assert_eq!(prod, Q::one());
}

#[test]
fn test_distributivity_exact() {
    // a * (b + c) == a * b + a * c on exact path
    let a = Q::new(2, 3).unwrap();
    let b = Q::new(1, 5).unwrap();
    let c = Q::new(1, 7).unwrap();

    let lhs = a.mul(b.add(c));
    let rhs = a.mul(b).add(a.mul(c));

    // Should be exact for small values
    assert_eq!(lhs.to_f64(), rhs.to_f64());
}

#[test]
fn test_canonicality_preserved() {
    let test_cases = [
        (2, 4),
        (6, 9),
        (10, 15),
        (-3, 6),
        (-8, -12),
    ];

    for (num, den) in test_cases {
        let q = Q::new(num, den).unwrap();
        // Creating again with canonical form should be idempotent
        let q2 = Q::new(q.numerator(), q.denominator()).unwrap();
        assert_eq!(q, q2);
    }
}

#[test]
fn test_bounds_preserved() {
    let test_cases = [
        (1, 2),
        (999, 1000),
        (1, 1000000),
    ];

    for (num, den) in test_cases {
        let q = Q::new(num, den).unwrap();
        assert!(q.numerator().abs() <= (1i64 << 62) - 1);
        assert!(q.denominator() > 0 && q.denominator() <= (1i64 << 62) - 1);
    }
}

#[test]
fn test_order_total() {
    let a = Q::new(1, 3).unwrap();
    let b = Q::new(1, 2).unwrap();
    let c = Q::new(2, 3).unwrap();

    // Transitivity
    assert!(a < b && b < c && a < c);

    // Antisymmetry
    assert!(!a.eq(&b) || !(a < b));
    assert!(a == a);

    // Totality
    assert!(a != b);
    assert!(a < b || a == b || a > b);
}

#[test]
fn test_signum() {
    let pos = Q::new(3, 5).unwrap();
    let zero = Q::zero();
    let neg = Q::new(-2, 7).unwrap();

    assert_eq!(pos.signum(), 1);
    assert_eq!(zero.signum(), 0);
    assert_eq!(neg.signum(), -1);
}

#[test]
fn test_unit_interval() {
    let tests = [
        (Q::zero(), true),
        (Q::one(), true),
        (Q::new(1, 2).unwrap(), true),
        (Q::new(3, 2).unwrap(), false),
        (Q::new(-1, 2).unwrap(), false),
    ];

    for (q, expected) in tests {
        assert_eq!(q.in_unit_interval(), expected);
    }
}

#[test]
fn test_negation_involution() {
    let a = Q::new(5, 7).unwrap();
    assert_eq!(a.neg().neg(), a);
}

#[test]
fn test_abs() {
    let pos = Q::new(3, 5).unwrap();
    let neg = Q::new(-3, 5).unwrap();

    assert_eq!(pos.abs(), pos);
    assert_eq!(neg.abs(), pos);
    assert_eq!(Q::zero().abs(), Q::zero());
}

#[test]
fn test_recip_involution() {
    let a = Q::new(5, 7).unwrap();
    assert_eq!(a.recip().unwrap().recip().unwrap(), a);
}

#[test]
fn test_min_max() {
    let a = Q::new(1, 3).unwrap();
    let b = Q::new(1, 2).unwrap();

    assert_eq!(a.min(b), a);
    assert_eq!(a.max(b), b);
}

#[test]
fn test_clamp() {
    let q = Q::new(1, 2).unwrap();
    let lo = Q::new(1, 4).unwrap();
    let hi = Q::new(3, 4).unwrap();

    assert_eq!(q.clamp(lo, hi), q);
    assert_eq!(Q::new(1, 8).unwrap().clamp(lo, hi), lo);
    assert_eq!(Q::new(7, 8).unwrap().clamp(lo, hi), hi);
}

#[test]
fn test_from_int_to_f64() {
    let a = Q::from_int(5).unwrap();
    assert_eq!(a.to_f64(), 5.0);

    let b = Q::from_int(-3).unwrap();
    assert_eq!(b.to_f64(), -3.0);
}

#[test]
fn test_from_decimal() {
    let q = Q::from_decimal(85, 2).unwrap();
    assert!((q.to_f64() - 0.85).abs() < 1e-10);

    let q2 = Q::from_decimal(5, 1).unwrap();
    assert_eq!(q2.to_f64(), 0.5);
}

#[test]
fn test_determinism() {
    let a = Q::new(17, 23).unwrap();
    let b = Q::new(13, 19).unwrap();

    let r1 = a.add(b);
    let r2 = a.add(b);

    assert_eq!(r1, r2);
    assert_eq!(r1.numerator(), r2.numerator());
    assert_eq!(r1.denominator(), r2.denominator());
}

#[test]
fn test_copy_trait() {
    let a = Q::new(3, 5).unwrap();
    let b = a; // Copy should allow this
    assert_eq!(a, b);
}

#[test]
fn test_hash_eq() {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};

    let a = Q::new(2, 4).unwrap();
    let b = Q::new(1, 2).unwrap();

    // Same canonical form should hash the same
    assert_eq!(a, b);

    let mut hasher_a = DefaultHasher::new();
    a.hash(&mut hasher_a);
    let hash_a = hasher_a.finish();

    let mut hasher_b = DefaultHasher::new();
    b.hash(&mut hasher_b);
    let hash_b = hasher_b.finish();

    assert_eq!(hash_a, hash_b);
}

#[test]
fn test_display() {
    let q = Q::new(3, 5).unwrap();
    assert_eq!(format!("{}", q), "3/5");

    let q_neg = Q::new(-2, 3).unwrap();
    assert_eq!(format!("{}", q_neg), "-2/3");
}
