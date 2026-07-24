// Differential tests against malachite-q (dev-only oracle, LGPL is fine here).
// Exact-path results must equal the oracle; rounded results ≤ R3 error bound.

use malachite_q::Rational;
use malachite_base::num::basic::traits::Zero as MZero;
use malachite_base::num::arithmetic::traits::Abs;
use the_q::{Q, Dir};
use the_q::convert::{from_decimal, from_f64_dir, to_f64};

const BOUND: i64 = (1i64 << 62) - 1;
const B: u32 = 60;

// ─── Helpers ─────────────────────────────────────────────────────────────────

fn to_rat(q: Q) -> Rational {
    Rational::from_signeds(q.num(), q.den())
}

fn rat_parts(n: i64, d: i64) -> Rational {
    Rational::from_signeds(n, d)
}

fn check_wf(q: Q, ctx: &str) {
    assert!(q.den() > 0, "{ctx}: den not > 0");
    assert!(q.den() <= BOUND, "{ctx}: den > BOUND");
    assert!(q.num().abs() <= BOUND, "{ctx}: |num| > BOUND");
    if q.num() == 0 {
        assert_eq!(q.den(), 1, "{ctx}: num=0 but den != 1");
    } else {
        assert_eq!(gcd(q.num().unsigned_abs() as u64, q.den() as u64), 1,
            "{ctx}: {}/{} not canonical", q.num(), q.den());
    }
}

fn gcd(a: u64, b: u64) -> u64 {
    if b == 0 { if a == 0 { 1 } else { a } } else { gcd(b, a % b) }
}

fn check_r3(result: Q, exact: &Rational, ctx: &str) {
    let r = to_rat(result);
    let diff: Rational = (r.clone() - exact.clone()).abs();
    // bound = 2^-B * max(1, |exact|)
    let abs_exact = exact.clone().abs();
    let one = Rational::from(1u32);
    let max_1_exact = if abs_exact > one { abs_exact } else { Rational::from(1u32) };
    // 2^-B = 1 / 2^B; split to avoid overflow: 1/(2^30 * 2^30)
    let two_pow_b = Rational::from(1u64)
        / (Rational::from(1u64 << 30) * Rational::from(1u64 << (B - 30)));
    let bound = two_pow_b * max_1_exact;
    assert!(diff <= bound, "{ctx}: |{} - exact| = {} > R3 bound", r, diff);
}

// ─── Exhaustive small-value tests ─────────────────────────────────────────────

#[test]
fn exhaustive_small_add() {
    for n1 in -8i64..=8 {
        for d1 in 1i64..=8 {
            for n2 in -8i64..=8 {
                for d2 in 1i64..=8 {
                    let a = Q::new(n1, d1).unwrap();
                    let b = Q::new(n2, d2).unwrap();
                    let r = a.add(b);
                    check_wf(r, "add");
                    let exact = rat_parts(n1, d1) + rat_parts(n2, d2);
                    assert_eq!(to_rat(r), exact,
                        "add({}/{}, {}/{}) got {} expected {}",
                        n1, d1, n2, d2, r, exact);
                }
            }
        }
    }
}

#[test]
fn exhaustive_small_mul() {
    for n1 in -8i64..=8 {
        for d1 in 1i64..=8 {
            for n2 in -8i64..=8 {
                for d2 in 1i64..=8 {
                    let a = Q::new(n1, d1).unwrap();
                    let b = Q::new(n2, d2).unwrap();
                    let r = a.mul(b);
                    check_wf(r, "mul");
                    let exact = rat_parts(n1, d1) * rat_parts(n2, d2);
                    assert_eq!(to_rat(r), exact,
                        "mul({}/{}, {}/{}) got {} expected {}",
                        n1, d1, n2, d2, r, exact);
                }
            }
        }
    }
}

#[test]
fn exhaustive_small_div() {
    for n1 in -8i64..=8 {
        for d1 in 1i64..=8 {
            for n2 in -8i64..=8 {
                for d2 in 1i64..=8 {
                    if n2 == 0 { continue; }
                    let a = Q::new(n1, d1).unwrap();
                    let b = Q::new(n2, d2).unwrap();
                    let r = a.div(b);
                    check_wf(r, "div");
                    let exact = rat_parts(n1, d1) / rat_parts(n2, d2);
                    assert_eq!(to_rat(r), exact,
                        "div({}/{}, {}/{}) got {} expected {}",
                        n1, d1, n2, d2, r, exact);
                }
            }
        }
    }
}

#[test]
fn exhaustive_small_cmp() {
    for n1 in -8i64..=8 {
        for d1 in 1i64..=8 {
            for n2 in -8i64..=8 {
                for d2 in 1i64..=8 {
                    let a = Q::new(n1, d1).unwrap();
                    let b = Q::new(n2, d2).unwrap();
                    let our = a.cmp(&b);
                    let oracle = rat_parts(n1, d1).cmp(&rat_parts(n2, d2));
                    assert_eq!(our, oracle,
                        "cmp({}/{}, {}/{}) got {:?} expected {:?}",
                        n1, d1, n2, d2, our, oracle);
                }
            }
        }
    }
}

// ─── Property tests ──────────────────────────────────────────────────────────

#[test]
fn canonicality_after_ops() {
    let pairs = [
        (Q::new(1, 3).unwrap(), Q::new(1, 6).unwrap()),
        (Q::new(7, 11).unwrap(), Q::new(3, 13).unwrap()),
        (Q::new(-5, 8).unwrap(), Q::new(3, 8).unwrap()),
    ];
    for (a, b) in pairs {
        check_wf(a.add(b), "add");
        check_wf(a.sub(b), "sub");
        check_wf(a.mul(b), "mul");
        if !b.is_zero() { check_wf(a.div(b), "div"); }
        check_wf(a.neg(), "neg");
        check_wf(a.abs(), "abs");
        check_wf(a.min_q(b), "min");
        check_wf(a.max_q(b), "max");
    }
}

#[test]
fn commutativity() {
    let pairs = [
        (Q::new(2, 3).unwrap(), Q::new(3, 5).unwrap()),
        (Q::new(-1, 7).unwrap(), Q::new(5, 11).unwrap()),
        (Q::new(0, 1).unwrap(), Q::new(7, 13).unwrap()),
    ];
    for (a, b) in pairs {
        let ab_rat = to_rat(a.add(b));
        let ba_rat = to_rat(b.add(a));
        assert_eq!(ab_rat, ba_rat, "add not commutative");

        let ab_rat = to_rat(a.mul(b));
        let ba_rat = to_rat(b.mul(a));
        assert_eq!(ab_rat, ba_rat, "mul not commutative");
    }
}

#[cfg(feature = "serde")]
#[test]
fn serde_roundtrip() {
    let qs = [Q::new(3,4).unwrap(), Q::new(-5,7).unwrap(), Q::zero(), Q::one()];
    for q in qs {
        let json = serde_json::to_string(&q).unwrap();
        let q2: Q = serde_json::from_str(&json).unwrap();
        assert_eq!(q, q2, "serde roundtrip failed for {}", q);
        check_wf(q2, "serde");
    }
}

#[test]
fn r1_exact_representable() {
    let a = Q::new(1, 1i64 << 30).unwrap();
    let b = Q::new(1, (1i64 << 30) + 1).unwrap();
    let r = a.add(b);
    check_wf(r, "R1 add");
    let exact = rat_parts(1, 1i64 << 30) + rat_parts(1, (1i64 << 30) + 1);
    check_r3(r, &exact, "small add R3");
}

#[test]
fn budget_edge_values() {
    let big = Q::new(BOUND - 1, BOUND).unwrap();
    check_wf(big, "budget edge");
    let r = big.add(Q::one());
    check_wf(r, "budget edge + 1");
}

#[test]
fn sign_edges() {
    assert!(Q::from_int(i64::MIN).is_none()); // |i64::MIN| overflows — excluded by I2
    assert!(Q::from_int(-BOUND).is_some());
    assert!(Q::from_int(BOUND).is_some());
    assert!(Q::from_int(BOUND + 1).is_none());
}

#[test]
fn fold_chain_error_bound() {
    let step = Q::new(1, 10_000).unwrap();
    let step_rat = rat_parts(1, 10_000);
    let mut acc = Q::zero();
    let mut acc_rat = Rational::ZERO;
    for _ in 0..10_000usize {
        acc = acc.add(step);
        acc_rat = acc_rat.clone() + step_rat.clone();
        check_wf(acc, "fold step");
    }
    check_r3(acc, &acc_rat, "10k fold chain");
}

#[test]
fn from_decimal_oracle() {
    let cases = [(85i64, 2u8), (1, 4), (333, 3), (0, 5), (9999, 4)];
    for (m, dp) in cases {
        let q = from_decimal(m, dp).unwrap();
        check_wf(q, "from_decimal");
        let scale = 10i128.pow(dp as u32);
        let exact = rat_parts(m, scale as i64);
        assert_eq!(to_rat(q), exact, "from_decimal({m}, {dp})");
    }
}

#[test]
fn from_f64_dir_exact_dyadic() {
    let cases = [0.5f64, 0.25, 0.125, 0.75, 1.0, -0.5, 3.0, 4.0, 0.0];
    for v in cases {
        let q = from_f64_dir(v, Dir::Nearest).unwrap();
        check_wf(q, "from_f64_dir");
        // Dyadic f64 values convert exactly; to_f64 round-trips.
        assert!((to_f64(q) - v).abs() < 1e-15,
            "from_f64_dir({v}) round-trip: got {}", to_f64(q));
    }
}
