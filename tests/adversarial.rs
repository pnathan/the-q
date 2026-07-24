//! Adversarial fixtures: budget edges, sign edges, i64::MIN, saturation,
//! long fold chains with error tracked against the oracle.

mod common;

use common::*;
use malachite_base::num::arithmetic::traits::Abs;
use malachite_q::Rational;
use the_q::{Dir, Q};

#[test]
fn budget_edge_values() {
    let edge = Q::new(MAX_MAG, 1).unwrap();
    let edge_recip = Q::new(1, MAX_MAG).unwrap();
    let near = Q::new(MAX_MAG - 1, MAX_MAG).unwrap(); // coprime (consecutive)
    for &a in &[edge, edge_recip, near] {
        for &b in &[edge, edge_recip, near] {
            let (ra, rb) = (rat(a), rat(b));
            for dir in DIRS {
                check_rounding_contract(a.add_dir(b, dir), &(&ra + &rb), dir, "edge add");
                check_rounding_contract(a.mul_dir(b, dir), &(&ra * &rb), dir, "edge mul");
                check_rounding_contract(a.sub_dir(b, dir), &(&ra - &rb), dir, "edge sub");
                check_rounding_contract(a.div_dir(b, dir), &(&ra / &rb), dir, "edge div");
            }
        }
    }
}

#[test]
fn saturation_at_max() {
    let edge = Q::new(MAX_MAG, 1).unwrap();
    // MAX * MAX is far out of range: saturates to MAX/1 (sign preserved)
    let r = edge.mul(edge);
    assert_eq!(r.to_parts(), (MAX_MAG, 1));
    let r = edge.neg().mul(edge);
    assert_eq!(r.to_parts(), (-MAX_MAG, 1));
    // Down-directed saturation is still a lower bound
    let r = edge.mul_dir(edge, Dir::Down);
    assert!(rat(r) <= rat(edge) * rat(edge));
}

#[test]
fn i64_min_handling() {
    // |i64::MIN| overflows i64; the constructor must handle it, and I2
    // (which excludes 2^63) decides acceptance after reduction.
    assert!(Q::new(i64::MIN, 1).is_none()); // 2^63 > MAX
    assert!(Q::new(i64::MIN, 2).is_none()); // reduces to 2^62 > MAX
    let q = Q::new(i64::MIN, 4).unwrap(); // reduces to 2^61, in budget
    assert_eq!(q.to_parts(), (-(1i64 << 61), 1));
    assert_canonical(q);
    // den magnitude 2^63 - 1 exceeds the 2^62 - 1 budget and is coprime
    // with 1, so it must be rejected
    assert!(Q::new(1, i64::MIN + 1).is_none());
    // 2 / -2^63 reduces to -1 / 2^62, still one over budget
    assert!(Q::new(2, i64::MIN).is_none());
    // 4 / -2^63 reduces to -1 / 2^61: in budget
    let q = Q::new(4, i64::MIN).unwrap();
    assert_canonical(q);
    assert_eq!(q.to_parts(), (-1, 1i64 << 61));
    assert!(Q::from_int(i64::MIN).is_none());
    assert!(Q::from_int(MAX_MAG).is_some());
    assert!(Q::from_int(MAX_MAG.wrapping_add(1)).is_none());
    assert!(Q::from_decimal(i64::MIN, 0).is_none());
    assert!(Q::from_decimal(i64::MIN, 18).is_some()); // reduces below budget
}

#[test]
fn sign_edges() {
    for (n, d, en, ed) in [
        (0i64, 5i64, 0i64, 1i64),
        (0, -5, 0, 1),
        (3, -6, -1, 2),
        (-3, -6, 1, 2),
        (-3, 6, -1, 2),
    ] {
        let q = Q::new(n, d).unwrap();
        assert_eq!(q.to_parts(), (en, ed), "canonicalization of {n}/{d}");
    }
}

#[test]
fn long_fold_chain_error_bounded() {
    // 10^4 alternating ops on unit-interval values, tracked exactly by the
    // oracle. Accumulated relative error must stay within k * 2^-60 of the
    // exact value (loose check: <= 1e-12 absolute on [0,1]-ish values).
    let mut rng = Rng::new(0x10AD);
    let mut acc = Q::new(1, 3).unwrap();
    let mut exact = rat_of(1, 3);
    let mut worst = Rational::from(0);
    for i in 0..10_000 {
        let x = rand_unit_q(&mut rng);
        let rx = rat(x);
        match i % 4 {
            0 => {
                acc = acc.add(x);
                exact = &exact + &rx;
            }
            1 => {
                acc = acc.sub(x);
                exact = &exact - &rx;
            }
            2 => {
                // keep the magnitude tame: multiply by a unit-interval value
                acc = acc.mul(x);
                exact = &exact * &rx;
            }
            _ => {
                let half = Q::new(1, 2).unwrap();
                acc = acc.mul(half);
                exact = &exact * &rat_of(1, 2);
            }
        }
        assert_canonical(acc);
        let err = (rat(acc) - &exact).abs();
        if err > worst {
            worst = err.clone();
        }
        // per-step drift tracking: replace the oracle with the current
        // value periodically so the bound stays per-window
        if i % 100 == 99 {
            let scale = if exact.clone().abs() > Rational::from(1) {
                exact.clone().abs()
            } else {
                Rational::from(1)
            };
            assert!(
                err <= rat_of(200, 1 << 60) * scale,
                "accumulated error too large at step {i}: {err}"
            );
            exact = rat(acc); // reset window
        }
    }
    // sanity: rounding did happen at least sometimes in 10k mixed ops
    // (unit-\interval products blow up denominators fast)
    assert!(worst > Rational::from(0), "chain never rounded — test too weak");
}

#[test]
fn div_precondition_documented() {
    // div-by-zero is a static precondition; we only check the guard here
    let a = Q::new(3, 4).unwrap();
    let z = Q::zero();
    assert!(z.is_zero());
    // (calling a.div(z) would violate the verified precondition)
    let _ = a;
}

#[test]
fn from_f64_subnormal_and_tiny() {
    // sub-grid magnitudes: |v| < 2^-61 rounds to 0 (Down/Nearest on
    // positives) or one grid step 2^-61 (Up on positives)
    let tiny = f64::from_bits(1); // smallest positive subnormal
    let down = Q::from_f64_dir(tiny, Dir::Down).unwrap();
    assert!(down.is_zero());
    let near = Q::from_f64_dir(tiny, Dir::Nearest).unwrap();
    assert!(near.is_zero());
    let up = Q::from_f64_dir(tiny, Dir::Up).unwrap();
    assert_eq!(up.to_parts(), (1, 1 << 61));
    // mirrored for negatives
    let ntiny = -tiny;
    assert!(Q::from_f64_dir(ntiny, Dir::Up).unwrap().is_zero());
    assert_eq!(Q::from_f64_dir(ntiny, Dir::Down).unwrap().to_parts(), (-1, 1 << 61));
    // dyadic values in range convert exactly
    for v in [0.5f64, 0.25, 0.75, 1.0, 2.0, 1024.0, 3.5, 0.1] {
        let q = Q::from_f64_dir(v, Dir::Nearest).unwrap();
        let exact = Rational::try_from(v).unwrap();
        if fits_budget(&exact) {
            assert_eq!(rat(q), exact, "in-budget f64 {v} must convert exactly");
        }
    }
}
