//! Property tests: canonicality, commutativity, determinism, order laws,
//! exact-path associativity, serde round-trip.

mod common;

use common::*;
use the_q::{Dir, Q};

#[test]
fn invariants_hold_after_every_op() {
    let mut rng = Rng::new(1);
    for _ in 0..3000 {
        let a = rand_q(&mut rng, 62, 62);
        let b = rand_q(&mut rng, 62, 62);
        for dir in DIRS {
            assert_canonical(a.add_dir(b, dir));
            assert_canonical(a.sub_dir(b, dir));
            assert_canonical(a.mul_dir(b, dir));
            if !b.is_zero() {
                assert_canonical(a.div_dir(b, dir));
            }
        }
        assert_canonical(a.min(b));
        assert_canonical(a.max(b));
    }
}

#[test]
fn add_mul_commutative_bit_exact() {
    let mut rng = Rng::new(2);
    for _ in 0..3000 {
        let a = rand_q(&mut rng, 62, 62);
        let b = rand_q(&mut rng, 62, 62);
        for dir in DIRS {
            assert_eq!(a.add_dir(b, dir), b.add_dir(a, dir), "add not commutative");
            assert_eq!(a.mul_dir(b, dir), b.mul_dir(a, dir), "mul not commutative");
        }
    }
}

#[test]
fn deterministic_across_repetition_and_threads() {
    let mut rng = Rng::new(3);
    let pairs: Vec<(Q, Q)> = (0..500)
        .map(|_| (rand_q(&mut rng, 62, 62), rand_q(&mut rng, 62, 62)))
        .collect();
    let run = |ps: &[(Q, Q)]| -> Vec<Q> {
        ps.iter().map(|&(a, b)| a.add(b).mul(a.sub(b))).collect()
    };
    let r1 = run(&pairs);
    let r2 = run(&pairs);
    assert_eq!(r1, r2);
    // byte-identical across threads
    let ps = pairs.clone();
    let handle = std::thread::spawn(move || run(&ps));
    assert_eq!(handle.join().unwrap(), r1);
}

#[test]
fn exact_path_associativity() {
    // small values: everything fits the budget, so (a+b)+c == a+(b+c)
    // and (a*b)*c == a*(b*c) bit-exactly.
    let mut rng = Rng::new(4);
    for _ in 0..2000 {
        let a = rand_q(&mut rng, 12, 12);
        let b = rand_q(&mut rng, 12, 12);
        let c = rand_q(&mut rng, 12, 12);
        assert_eq!(a.add(b).add(c), a.add(b.add(c)));
        assert_eq!(a.mul(b).mul(c), a.mul(b.mul(c)));
        assert_eq!(a.mul(b.add(c)), a.mul(b).add(a.mul(c)));
    }
}

#[test]
fn order_is_total_and_consistent() {
    let mut rng = Rng::new(5);
    let mut xs: Vec<Q> = (0..500).map(|_| rand_q(&mut rng, 40, 40)).collect();
    xs.sort(); // uses the Ord glue -> verified cmp_q
    for w in xs.windows(2) {
        assert!(w[0].le(w[1]));
        assert!(rat(w[0]) <= rat(w[1]));
    }
    for _ in 0..1000 {
        let a = rand_q(&mut rng, 40, 40);
        let b = rand_q(&mut rng, 40, 40);
        // totality + antisymmetry through structural equality
        assert!(a.le(b) || b.le(a));
        if a.le(b) && b.le(a) {
            assert_eq!(a, b);
        }
    }
}

#[test]
fn min_max_clamp_laws() {
    let mut rng = Rng::new(6);
    for _ in 0..2000 {
        let a = rand_q(&mut rng, 40, 40);
        let b = rand_q(&mut rng, 40, 40);
        let (lo, hi) = if a.le(b) { (a, b) } else { (b, a) };
        let x = rand_q(&mut rng, 40, 40);
        let c = x.clamp(lo, hi);
        assert!(lo.le(c) && c.le(hi));
        if lo.le(x) && x.le(hi) {
            assert_eq!(c, x);
        }
        assert_eq!(a.min(b), if a.le(b) { a } else { b });
        assert_eq!(a.max(b), if b.le(a) { a } else { b });
        assert_eq!(x.neg().neg(), x);
        if !x.is_zero() {
            assert_eq!(x.recip().recip(), x);
        }
    }
}

#[test]
fn unit_interval_predicate() {
    assert!(Q::zero().in_unit_interval());
    assert!(Q::one().in_unit_interval());
    assert!(Q::new(1, 2).unwrap().in_unit_interval());
    assert!(!Q::new(-1, 2).unwrap().in_unit_interval());
    assert!(!Q::new(3, 2).unwrap().in_unit_interval());
    let mut rng = Rng::new(7);
    for _ in 0..1000 {
        let q = rand_unit_q(&mut rng);
        assert!(q.in_unit_interval());
    }
}

#[test]
fn signum_zero_one() {
    assert_eq!(Q::zero().signum(), 0);
    assert!(Q::zero().is_zero());
    assert!(Q::one().is_one());
    assert_eq!(Q::new(-3, 7).unwrap().signum(), -1);
    assert_eq!(Q::new(3, 7).unwrap().signum(), 1);
}

#[test]
fn display_format() {
    assert_eq!(Q::new(-6, 4).unwrap().to_string(), "-3/2");
    assert_eq!(Q::zero().to_string(), "0/1");
    assert_eq!(Q::from_decimal(85, 2).unwrap().to_string(), "17/20");
}

#[test]
fn hash_consistent_with_eq() {
    use std::collections::HashSet;
    let mut set = HashSet::new();
    set.insert(Q::new(1, 2).unwrap());
    set.insert(Q::new(2, 4).unwrap()); // same value, same canonical form
    set.insert(Q::new(-3, -6).unwrap()); // 1/2 again via double negation
    assert_eq!(set.len(), 1);
}

#[test]
fn nary_helpers() {
    let xs: Vec<Q> = (1..=10).map(|i| Q::new(1, i).unwrap()).collect();
    let s = Q::sum(&xs);
    assert_canonical(s);
    // H_10 == 7381/2520 exactly (all partials fit the budget)
    assert_eq!(rat(s), rat_of(7381, 2520));
    let p = Q::product(&xs);
    assert_eq!(rat(p), rat_of(1, 3628800));
    let wm = Q::weighted_mean(&[
        (Q::new(1, 2).unwrap(), Q::new(1, 1).unwrap()),
        (Q::new(1, 4).unwrap(), Q::new(3, 1).unwrap()),
    ])
    .unwrap();
    // (1/2*1 + 1/4*3) / 4 == 5/16
    assert_eq!(rat(wm), rat_of(5, 16));
    assert!(Q::weighted_mean(&[]).is_none());
}

#[cfg(feature = "serde")]
#[test]
fn serde_round_trip_exact() {
    let mut rng = Rng::new(8);
    for _ in 0..2000 {
        let q = rand_q(&mut rng, 62, 62);
        let s = serde_json::to_string(&q).unwrap();
        let back: Q = serde_json::from_str(&s).unwrap();
        assert_eq!(q, back, "serde round-trip must be exact");
    }
    // rejects invalid input
    assert!(serde_json::from_str::<Q>("[1, 0]").is_err());
    // non-canonical input is canonicalized, not rejected
    let q: Q = serde_json::from_str("[2, 4]").unwrap();
    assert_eq!(q, Q::new(1, 2).unwrap());
}
