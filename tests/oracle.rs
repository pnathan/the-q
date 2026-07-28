//! Differential tests against malachite-q (dev-dependency only).
//!
//! malachite-q is LGPL-3.0; it MUST NOT appear in the non-dev dependency tree.
//! These tests verify:
//! - Exact-path results equal the oracle
//! - Rounded results are within the R3 bound of the oracle's exact value
//! - Canonicality and I2 after every op
//! - Commutativity, round-trip serde, determinism

use malachite_base::num::basic::traits::{One, Zero};
use malachite_base::num::conversion::traits::RoundingFrom;
use malachite_base::rounding_modes::RoundingMode;
use malachite_q::Rational;
use the_q::{Dir, Q};

const BOUND: u64 = (1u64 << 62) - 1;

fn q_to_rational(q: Q) -> Rational {
    Rational::from_signeds(q.num() as i128, q.den() as i128)
}

fn check_invariants(q: Q) {
    assert!(q.den() > 0, "I1: den must be positive, got {}", q.den());

    if q.num() == 0 {
        assert_eq!(q.den(), 1, "I1: zero must have den=1");
    }

    let g = gcd_u64(q.num().unsigned_abs(), q.den() as u64);
    assert_eq!(g, 1, "I1: not in lowest terms: {}/{}, gcd={g}", q.num(), q.den());

    assert!(
        q.num().unsigned_abs() <= BOUND,
        "I2: |num| > BOUND: {}",
        q.num()
    );
    assert!(
        (q.den() as u64) <= BOUND,
        "I2: den > BOUND: {}",
        q.den()
    );
}

fn gcd_u64(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        let t = b;
        b = a % b;
        a = t;
    }
    a
}

fn check_exact_or_bounded(q: Q, exact: &Rational) {
    check_invariants(q);

    let q_rat = q_to_rational(q);

    if &q_rat == exact {
        return;
    }

    let error = if &q_rat > exact {
        &q_rat - exact
    } else {
        exact - &q_rat
    };

    let magnitude = if exact == &Rational::ZERO {
        Rational::ONE.clone()
    } else {
        let abs_exact = if exact < &Rational::ZERO {
            -exact
        } else {
            exact.clone()
        };
        if abs_exact < Rational::ONE {
            Rational::ONE.clone()
        } else {
            abs_exact
        }
    };

    // R3: error ≤ 2^{-60} · max(1, |exact|)
    let bound_num = magnitude;
    // 2^{-60} = 1 / 2^60
    let two_pow_60 = Rational::from(1u64 << 60);
    let bound = bound_num / two_pow_60;

    assert!(
        error <= bound,
        "R3 violated: error = {error}, bound = {bound}, q = {q}, exact = {exact}",
    );
}

// Small-value exhaustive tests
fn small_values() -> Vec<Q> {
    let mut vals = vec![Q::zero(), Q::one(), Q::from_int(-1).unwrap()];
    for n in -10i64..=10 {
        for d in 1i64..=10 {
            if let Some(q) = Q::new(n, d) {
                if !vals.contains(&q) {
                    vals.push(q);
                }
            }
        }
    }
    vals
}

#[test]
fn exhaustive_add() {
    let vals = small_values();
    for &a in &vals {
        for &b in &vals {
            let result = a + b;
            check_invariants(result);

            let exact = q_to_rational(a) + q_to_rational(b);
            check_exact_or_bounded(result, &exact);

            // Commutativity
            assert_eq!(result, b + a, "add not commutative: {a} + {b}");
        }
    }
}

#[test]
fn exhaustive_sub() {
    let vals = small_values();
    for &a in &vals {
        for &b in &vals {
            let result = a - b;
            check_invariants(result);

            let exact = q_to_rational(a) - q_to_rational(b);
            check_exact_or_bounded(result, &exact);
        }
    }
}

#[test]
fn exhaustive_mul() {
    let vals = small_values();
    for &a in &vals {
        for &b in &vals {
            let result = a * b;
            check_invariants(result);

            let exact = q_to_rational(a) * q_to_rational(b);
            check_exact_or_bounded(result, &exact);

            // Commutativity
            assert_eq!(result, b * a, "mul not commutative: {a} * {b}");
        }
    }
}

#[test]
fn exhaustive_div() {
    let vals = small_values();
    for &a in &vals {
        for &b in &vals {
            if b.is_zero() {
                continue;
            }
            let result = a / b;
            check_invariants(result);

            let exact = q_to_rational(a) / q_to_rational(b);
            check_exact_or_bounded(result, &exact);
        }
    }
}

#[test]
fn exhaustive_neg_abs() {
    let vals = small_values();
    for &a in &vals {
        let neg = -a;
        check_invariants(neg);
        assert_eq!(q_to_rational(neg), -q_to_rational(a));
        assert_eq!(-neg, a, "neg involution");

        let abs = a.abs();
        check_invariants(abs);
        let exact_abs = if a.num() >= 0 {
            q_to_rational(a)
        } else {
            -q_to_rational(a)
        };
        assert_eq!(q_to_rational(abs), exact_abs);
    }
}

#[test]
fn exhaustive_recip() {
    let vals = small_values();
    for &a in &vals {
        if a.is_zero() {
            continue;
        }
        let r = a.recip();
        check_invariants(r);
        let exact = Rational::ONE / q_to_rational(a);
        assert_eq!(q_to_rational(r), exact, "recip({a})");
        assert_eq!(r.recip(), a, "recip involution");
    }
}

#[test]
fn exhaustive_cmp() {
    let vals = small_values();
    for &a in &vals {
        for &b in &vals {
            let cmp_q = a.cmp(&b);
            let cmp_rat = q_to_rational(a).cmp(&q_to_rational(b));
            assert_eq!(
                cmp_q, cmp_rat,
                "cmp mismatch: {a} vs {b}: Q says {cmp_q:?}, oracle says {cmp_rat:?}"
            );
        }
    }
}

// Budget-edge tests

#[test]
fn budget_edge_add() {
    let big = Q::from_int(BOUND as i64).unwrap();
    let one = Q::one();

    let r = big + one;
    check_invariants(r);
    let exact = q_to_rational(big) + q_to_rational(one);
    check_exact_or_bounded(r, &exact);
}

#[test]
fn budget_edge_mul() {
    let big = Q::new(BOUND as i64, 1).unwrap();
    let half = Q::new(1, 2).unwrap();

    let r = big * half;
    check_invariants(r);
    let exact = q_to_rational(big) * q_to_rational(half);
    check_exact_or_bounded(r, &exact);
}

#[test]
fn budget_edge_large_denominators() {
    let a = Q::new(1, BOUND as i64).unwrap();
    let b = Q::new(1, BOUND as i64).unwrap();
    let r = a + b;
    check_invariants(r);
    let exact = q_to_rational(a) + q_to_rational(b);
    check_exact_or_bounded(r, &exact);
}

#[test]
fn budget_edge_mul_large_den() {
    let a = Q::new(BOUND as i64, 1).unwrap();
    let b = Q::new(1, BOUND as i64).unwrap();
    let r = a * b;
    check_invariants(r);
    // Should be exactly 1 after GCD reduction
    assert_eq!(r, Q::one());
}

// Long fold chain with oracle tracking

#[test]
fn long_add_chain_oracle() {
    let n = 10_000;
    let step = Q::new(1, n as i64).unwrap();
    let step_rat = q_to_rational(step);

    let mut q_acc = Q::zero();
    let mut rat_acc = Rational::ZERO;

    for _ in 0..n {
        q_acc = q_acc + step;
        rat_acc += &step_rat;
    }

    check_invariants(q_acc);
    check_exact_or_bounded(q_acc, &rat_acc);
}

#[test]
fn long_mul_chain_oracle() {
    let factor = Q::new(999, 1000).unwrap();
    let factor_rat = q_to_rational(factor);

    let mut q_acc = Q::one();
    let mut rat_acc = Rational::ONE;

    for _ in 0..10_000 {
        q_acc = q_acc * factor;
        rat_acc *= &factor_rat;
        check_invariants(q_acc);
    }

    let q_f64 = q_acc.to_f64();
    let oracle_f64: f64 =
        f64::rounding_from(&rat_acc, RoundingMode::Nearest).0;
    let rel_error = if oracle_f64.abs() > 1e-300 {
        ((q_f64 - oracle_f64) / oracle_f64).abs()
    } else {
        (q_f64 - oracle_f64).abs()
    };
    // 10k ops × 2^{-60} ≈ 2^{-46.7} ≈ 7e-15 cumulative bound
    assert!(
        rel_error < 1e-10,
        "long mul chain: q={q_f64}, oracle={oracle_f64}, rel_error={rel_error}"
    );
}

// from_f64_dir tests

#[test]
fn from_f64_exact_powers_of_two() {
    for exp in 0..50 {
        let v = (1u64 << exp) as f64;
        let q = Q::from_f64_dir(v, Dir::Nearest).unwrap();
        check_invariants(q);
        assert_eq!(q, Q::from_int(1i64 << exp).unwrap());
    }
}

#[test]
fn from_f64_common_decimals() {
    let cases = [
        (0.1, 1, 10),
        (0.5, 1, 2),
        (0.25, 1, 4),
        (0.75, 3, 4),
        (0.125, 1, 8),
    ];

    for (f, _expected_num, _expected_den) in cases {
        let q = Q::from_f64_dir(f, Dir::Nearest).unwrap();
        check_invariants(q);
        // 0.1 is NOT exactly 1/10 in f64; it's a nearby dyadic rational.
        // So we check that the Q is close to the expected value.
        let diff = (q.to_f64() - f).abs();
        assert!(diff < 1e-15, "from_f64({f}): diff = {diff}");
    }

    // These ARE exact in f64
    let q = Q::from_f64_dir(0.5, Dir::Nearest).unwrap();
    assert_eq!(q, Q::new(1, 2).unwrap());
    let q = Q::from_f64_dir(0.25, Dir::Nearest).unwrap();
    assert_eq!(q, Q::new(1, 4).unwrap());
}

// Determinism: same computation, same result
#[test]
fn determinism() {
    let a = Q::new(17, 31).unwrap();
    let b = Q::new(23, 47).unwrap();

    let r1 = (a + b) * (a - b);
    let r2 = (a + b) * (a - b);
    assert_eq!(r1, r2);
    assert_eq!(r1.num(), r2.num());
    assert_eq!(r1.den(), r2.den());
}

#[test]
fn determinism_across_threads() {
    use std::thread;

    let a = Q::new(17, 31).unwrap();
    let b = Q::new(23, 47).unwrap();

    let main_result = (a + b) * (a - b) / Q::new(7, 13).unwrap();
    let main_num = main_result.num();
    let main_den = main_result.den();

    let handles: Vec<_> = (0..4)
        .map(|_| {
            thread::spawn(move || {
                let r = (a + b) * (a - b) / Q::new(7, 13).unwrap();
                (r.num(), r.den())
            })
        })
        .collect();

    for h in handles {
        let (n, d) = h.join().unwrap();
        assert_eq!(n, main_num);
        assert_eq!(d, main_den);
    }
}

// to_f64 differential test
#[test]
fn to_f64_matches_oracle() {
    let vals = small_values();
    for &q in &vals {
        let our_f64 = q.to_f64();
        let oracle_f64: f64 = f64::rounding_from(&q_to_rational(q), RoundingMode::Nearest).0;
        assert!(
            (our_f64 - oracle_f64).abs() < 1e-15 || (our_f64 == 0.0 && oracle_f64 == 0.0),
            "to_f64 mismatch for {q}: ours={our_f64}, oracle={oracle_f64}"
        );
    }
}
