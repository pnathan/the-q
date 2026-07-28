use proptest::prelude::*;
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};
use the_q::{Dir, Q};

const BOUND: u64 = (1u64 << 62) - 1;

fn arb_q() -> impl Strategy<Value = Q> {
    (-(BOUND as i64)..=(BOUND as i64), 1i64..=(BOUND as i64)).prop_map(|(n, d)| {
        Q::new(n, d).unwrap()
    })
}

fn arb_nonzero_q() -> impl Strategy<Value = Q> {
    arb_q().prop_filter("nonzero", |q| !q.is_zero())
}

fn arb_small_q() -> impl Strategy<Value = Q> {
    (-1000i64..=1000, 1i64..=1000).prop_map(|(n, d)| Q::new(n, d).unwrap())
}

fn arb_small_nonzero_q() -> impl Strategy<Value = Q> {
    arb_small_q().prop_filter("nonzero", |q| !q.is_zero())
}

fn check_invariants(q: Q) {
    assert!(q.den() > 0, "I1: den must be positive");
    assert!(q.num().unsigned_abs() <= BOUND, "I2: |num| > BOUND");
    assert!((q.den() as u64) <= BOUND, "I2: den > BOUND");
    if q.num() == 0 {
        assert_eq!(q.den(), 1, "I1: zero must have den=1");
    }
    let g = gcd_u64(q.num().unsigned_abs(), q.den() as u64);
    assert_eq!(g, 1, "I1: not reduced, gcd={g}");
}

fn gcd_u64(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        let t = b;
        b = a % b;
        a = t;
    }
    a
}

// ============================================================
// Invariant preservation
// ============================================================

proptest! {
    #[test]
    fn invariant_construction(n in -(BOUND as i64)..=(BOUND as i64), d in 1i64..=(BOUND as i64)) {
        let q = Q::new(n, d).unwrap();
        check_invariants(q);
    }

    #[test]
    fn invariant_add(a in arb_q(), b in arb_q()) {
        check_invariants(a + b);
    }

    #[test]
    fn invariant_sub(a in arb_q(), b in arb_q()) {
        check_invariants(a - b);
    }

    #[test]
    fn invariant_mul(a in arb_q(), b in arb_q()) {
        check_invariants(a * b);
    }

    #[test]
    fn invariant_div(a in arb_q(), b in arb_nonzero_q()) {
        check_invariants(a / b);
    }

    #[test]
    fn invariant_neg(a in arb_q()) {
        check_invariants(-a);
    }

    #[test]
    fn invariant_abs(a in arb_q()) {
        check_invariants(a.abs());
    }

    #[test]
    fn invariant_recip(a in arb_nonzero_q()) {
        check_invariants(a.recip());
    }
}

// ============================================================
// Commutativity
// ============================================================

proptest! {
    #[test]
    fn add_commutative(a in arb_q(), b in arb_q()) {
        prop_assert_eq!(a + b, b + a);
    }

    #[test]
    fn mul_commutative(a in arb_q(), b in arb_q()) {
        prop_assert_eq!(a * b, b * a);
    }
}

// ============================================================
// Identity elements
// ============================================================

proptest! {
    #[test]
    fn add_identity(a in arb_q()) {
        prop_assert_eq!(a + Q::zero(), a);
        prop_assert_eq!(Q::zero() + a, a);
    }

    #[test]
    fn mul_identity(a in arb_q()) {
        prop_assert_eq!(a * Q::one(), a);
        prop_assert_eq!(Q::one() * a, a);
    }

    #[test]
    fn mul_zero(a in arb_q()) {
        prop_assert_eq!(a * Q::zero(), Q::zero());
        prop_assert_eq!(Q::zero() * a, Q::zero());
    }
}

// ============================================================
// Involutions
// ============================================================

proptest! {
    #[test]
    fn neg_involution(a in arb_q()) {
        prop_assert_eq!(-(-a), a);
    }

    #[test]
    fn recip_involution(a in arb_nonzero_q()) {
        prop_assert_eq!(a.recip().recip(), a);
    }

    #[test]
    fn abs_idempotent(a in arb_q()) {
        prop_assert_eq!(a.abs().abs(), a.abs());
    }
}

// ============================================================
// Additive inverse
// ============================================================

proptest! {
    #[test]
    fn add_neg_is_zero(a in arb_small_q()) {
        let r = a + (-a);
        prop_assert_eq!(r, Q::zero());
    }
}

// ============================================================
// Multiplicative inverse (exact path for small values)
// ============================================================

proptest! {
    #[test]
    fn mul_recip_is_one(a in arb_small_nonzero_q()) {
        let r = a * a.recip();
        prop_assert_eq!(r, Q::one());
    }
}

// ============================================================
// Ordering properties
// ============================================================

proptest! {
    #[test]
    fn ord_reflexive(a in arb_q()) {
        prop_assert!(a <= a);
        prop_assert!(a >= a);
        prop_assert_eq!(a, a);
    }

    #[test]
    fn ord_neg_reverses(a in arb_q(), b in arb_q()) {
        if a < b {
            prop_assert!(-a > -b);
        } else if a > b {
            prop_assert!(-a < -b);
        } else {
            prop_assert_eq!(-a, -b);
        }
    }

    #[test]
    fn abs_non_negative(a in arb_q()) {
        prop_assert!(a.abs() >= Q::zero());
    }

    #[test]
    fn abs_neg_eq(a in arb_q()) {
        prop_assert_eq!(a.abs(), (-a).abs());
    }
}

// ============================================================
// Directed rounding contracts
// ============================================================

proptest! {
    #[test]
    fn directed_rounding_order(a in arb_q(), b in arb_q()) {
        let down = a.add_dir(b, Dir::Down);
        let up = a.add_dir(b, Dir::Up);
        let near = a.add_dir(b, Dir::Nearest);

        check_invariants(down);
        check_invariants(up);
        check_invariants(near);

        prop_assert!(down <= up, "down={down} > up={up}");
        prop_assert!(near >= down, "nearest={near} < down={down}");
        prop_assert!(near <= up, "nearest={near} > up={up}");
    }

    #[test]
    fn directed_mul_order(a in arb_q(), b in arb_q()) {
        let down = a.mul_dir(b, Dir::Down);
        let up = a.mul_dir(b, Dir::Up);
        let near = a.mul_dir(b, Dir::Nearest);

        check_invariants(down);
        check_invariants(up);
        check_invariants(near);

        prop_assert!(down <= up, "mul: down={down} > up={up}");
        prop_assert!(near >= down, "mul: nearest={near} < down={down}");
        prop_assert!(near <= up, "mul: nearest={near} > up={up}");
    }

    #[test]
    fn directed_sub_order(a in arb_q(), b in arb_q()) {
        let down = a.sub_dir(b, Dir::Down);
        let up = a.sub_dir(b, Dir::Up);

        check_invariants(down);
        check_invariants(up);

        prop_assert!(down <= up);
    }

    #[test]
    fn directed_div_order(a in arb_q(), b in arb_nonzero_q()) {
        let down = a.div_dir(b, Dir::Down);
        let up = a.div_dir(b, Dir::Up);

        check_invariants(down);
        check_invariants(up);

        prop_assert!(down <= up);
    }
}

// ============================================================
// R3 error bound (via f64 approximation for large random values)
// ============================================================

proptest! {
    #[test]
    fn r3_bound_add(a in arb_q(), b in arb_q()) {
        let result = a + b;
        check_invariants(result);

        let exact_f64 = a.to_f64() + b.to_f64();
        let result_f64 = result.to_f64();
        let error = (result_f64 - exact_f64).abs();
        let magnitude = exact_f64.abs().max(1.0);
        let bound = magnitude / (1u64 << 60) as f64;

        // Allow extra tolerance for f64 rounding in the check itself
        prop_assert!(
            error <= bound * 2.0 + 1e-10,
            "R3 violated: error={error}, bound={bound}"
        );
    }

    #[test]
    fn r3_bound_mul(a in arb_q(), b in arb_q()) {
        let result = a * b;
        check_invariants(result);

        let exact_f64 = a.to_f64() * b.to_f64();
        let result_f64 = result.to_f64();
        let error = (result_f64 - exact_f64).abs();
        let magnitude = exact_f64.abs().max(1.0);
        let bound = magnitude / (1u64 << 60) as f64;

        prop_assert!(
            error <= bound * 2.0 + 1e-10,
            "R3 violated: error={error}, bound={bound}"
        );
    }
}

// ============================================================
// from_f64 round-trip
// ============================================================

proptest! {
    #[test]
    fn from_f64_preserves_invariants(v in -1e15f64..1e15f64) {
        if let Some(q) = Q::from_f64_dir(v, Dir::Nearest) {
            check_invariants(q);
            let back = q.to_f64();
            let error = (back - v).abs();
            let magnitude = v.abs().max(1.0);
            prop_assert!(
                error <= magnitude * 1e-15,
                "from_f64 round-trip: v={v}, back={back}, error={error}"
            );
        }
    }

    #[test]
    fn from_f64_directed(v in 0.001f64..1e10f64) {
        if let (Some(down), Some(up)) = (
            Q::from_f64_dir(v, Dir::Down),
            Q::from_f64_dir(v, Dir::Up),
        ) {
            check_invariants(down);
            check_invariants(up);
            prop_assert!(down <= up, "from_f64: down={down} > up={up}");
        }
    }
}

// ============================================================
// Structural equality = mathematical equality (canonical form)
// ============================================================

proptest! {
    #[test]
    fn canonical_form_unique(
        n in -100i64..=100,
        d in 1i64..=100,
        k in 1i64..=100,
    ) {
        let q1 = Q::new(n, d).unwrap();
        let q2 = Q::new(n * k, d * k).unwrap();
        prop_assert_eq!(q1, q2);
        prop_assert_eq!(q1.num(), q2.num());
        prop_assert_eq!(q1.den(), q2.den());
    }
}

// ============================================================
// Distributivity (exact path only, small values)
// ============================================================

proptest! {
    #[test]
    fn distributive_small(
        a in arb_small_q(),
        b in arb_small_q(),
        c in arb_small_q(),
    ) {
        let lhs = a * (b + c);
        let rhs = a * b + a * c;
        prop_assert_eq!(lhs, rhs);
    }
}

// ============================================================
// Associativity (exact path only, small values)
// ============================================================

proptest! {
    #[test]
    fn add_associative_small(
        a in arb_small_q(),
        b in arb_small_q(),
        c in arb_small_q(),
    ) {
        prop_assert_eq!((a + b) + c, a + (b + c));
    }

    #[test]
    fn mul_associative_small(
        a in arb_small_q(),
        b in arb_small_q(),
        c in arb_small_q(),
    ) {
        prop_assert_eq!((a * b) * c, a * (b * c));
    }
}

// ============================================================
// Min / Max / Clamp
// ============================================================

proptest! {
    #[test]
    fn min_max_consistent(a in arb_q(), b in arb_q()) {
        let mn = a.min(b);
        let mx = a.max(b);
        prop_assert!(mn <= mx);
        prop_assert!(mn == a || mn == b);
        prop_assert!(mx == a || mx == b);
    }

    #[test]
    fn clamp_in_range(
        v in arb_small_q(),
        lo in arb_small_q(),
        hi in arb_small_q(),
    ) {
        let (lo, hi) = if lo <= hi { (lo, hi) } else { (hi, lo) };
        let c = v.clamp(lo, hi);
        prop_assert!(c >= lo);
        prop_assert!(c <= hi);
    }
}

// ============================================================
// Signum
// ============================================================

proptest! {
    #[test]
    fn signum_correct(a in arb_q()) {
        let s = a.signum();
        if a.num() > 0 {
            prop_assert_eq!(s, 1);
        } else if a.num() < 0 {
            prop_assert_eq!(s, -1);
        } else {
            prop_assert_eq!(s, 0);
        }
    }
}

// ============================================================
// Determinism (byte-identical results across runs)
// ============================================================

fn hash_of(q: Q) -> u64 {
    let mut h = DefaultHasher::new();
    q.hash(&mut h);
    h.finish()
}

proptest! {
    #[test]
    fn deterministic_add(a in arb_q(), b in arb_q()) {
        let r1 = a + b;
        let r2 = a + b;
        prop_assert_eq!(r1.num(), r2.num());
        prop_assert_eq!(r1.den(), r2.den());
        prop_assert_eq!(hash_of(r1), hash_of(r2));
    }

    #[test]
    fn deterministic_mul(a in arb_q(), b in arb_q()) {
        let r1 = a * b;
        let r2 = a * b;
        prop_assert_eq!(r1.num(), r2.num());
        prop_assert_eq!(r1.den(), r2.den());
        prop_assert_eq!(hash_of(r1), hash_of(r2));
    }
}

// ============================================================
// Constructor rejection of out-of-range values
// ============================================================

#[test]
fn constructor_rejects_i64_min() {
    assert!(Q::new(i64::MIN, 1).is_none());
    assert!(Q::new(1, i64::MIN).is_none());
    // i64::MIN / i64::MIN reduces to 1/1 — valid after GCD reduction
    assert_eq!(Q::new(i64::MIN, i64::MIN), Some(Q::one()));
}

#[test]
fn constructor_rejects_zero_denominator() {
    assert!(Q::new(1, 0).is_none());
    assert!(Q::new(0, 0).is_none());
}

proptest! {
    #[test]
    fn constructor_rejects_over_budget(
        n in (BOUND as i64 + 1)..=i64::MAX,
    ) {
        // d=1 ensures GCD reduction cannot shrink |n| below budget
        prop_assert!(Q::new(n, 1).is_none());
    }
}

// ============================================================
// from_f64_dir edge cases
// ============================================================

proptest! {
    #[test]
    fn from_f64_subnormal_no_panic(
        bits in 1u64..=(((1u64 << 52) - 1)),
    ) {
        // Subnormals: exponent bits = 0, fraction bits != 0
        let v = f64::from_bits(bits);
        if let Some(q) = Q::from_f64_dir(v, Dir::Nearest) {
            check_invariants(q);
        }
        // Negative subnormal
        let v_neg = f64::from_bits(bits | (1u64 << 63));
        if let Some(q) = Q::from_f64_dir(v_neg, Dir::Nearest) {
            check_invariants(q);
        }
    }

    #[test]
    fn from_f64_large_returns_none(exp_offset in 62u32..=1000) {
        // Values with magnitude >= 2^62 should return None
        let v = 2.0f64.powi(exp_offset as i32);
        prop_assert!(Q::from_f64_dir(v, Dir::Nearest).is_none());
        prop_assert!(Q::from_f64_dir(-v, Dir::Nearest).is_none());
    }
}

// ============================================================
// Serde round-trip
// ============================================================

#[cfg(feature = "serde")]
mod serde_tests {
    use super::*;

    proptest! {
        #[test]
        fn serde_json_round_trip(a in arb_q()) {
            let json = serde_json::to_string(&a).unwrap();
            let back: Q = serde_json::from_str(&json).unwrap();
            prop_assert_eq!(a, back);
            prop_assert_eq!(a.num(), back.num());
            prop_assert_eq!(a.den(), back.den());
        }
    }
}
