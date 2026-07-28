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

#[test]
fn int_pow_behavior() {
    let half = Q::new(1, 2).unwrap();
    assert_eq!(half.int_pow(0), Q::one());
    assert_eq!(half.int_pow(10), Q::new(1, 1024).unwrap());
    let x = Q::new(3, 7).unwrap();
    // matches the product fold of e copies
    let xs = vec![x; 13];
    assert_eq!(x.int_pow(13), Q::product(&xs));
}

#[test]
fn interval_ops_enclose() {
    use the_q::interval::QI;
    let a = QI::new_qi(Q::new(1, 3).unwrap(), Q::new(1, 2).unwrap()).unwrap();
    let b = QI::new_qi(Q::new(1, 7).unwrap(), Q::new(2, 7).unwrap()).unwrap();
    // add: [1/3+1/7, 1/2+2/7] = [10/21, 11/14], small values so exact
    let s = a.add(b);
    assert_eq!(rat(s.lo), rat_of(10, 21));
    assert_eq!(rat(s.hi), rat_of(11, 14));
    // sub: [1/3-2/7, 1/2-1/7] = [1/21, 5/14]
    let d = a.sub(b);
    assert_eq!(rat(d.lo), rat_of(1, 21));
    assert_eq!(rat(d.hi), rat_of(5, 14));
    // mul (nonneg): [1/21, 1/7]
    let p = a.mul_nonneg(b);
    assert_eq!(rat(p.lo), rat_of(1, 21));
    assert_eq!(rat(p.hi), rat_of(1, 7));
    // neg: [-1/2, -1/3]
    let n = a.neg();
    assert_eq!(rat(n.lo), rat_of(-1, 2));
    assert_eq!(rat(n.hi), rat_of(-1, 3));
    // endpoints stay ordered even when rounding kicks in
    let mut rng = Rng::new(0x1E7);
    for _ in 0..500 {
        let x = QI::point(rand_unit_q(&mut rng));
        let y = QI::point(rand_unit_q(&mut rng));
        let z = x.add(y).mul_nonneg(QI::point(rand_unit_q(&mut rng)));
        assert!(z.lo.le(z.hi));
        assert_canonical(z.lo);
        assert_canonical(z.hi);
    }
}

#[test]
fn fold_error_within_v8_bound() {
    // 1000 unit-interval multiplications: |result - exact| <= k * 2^-59.
    let mut rng = Rng::new(0xF01D);
    let xs: Vec<Q> = (0..1000)
        .map(|_| {
            let q = rand_unit_q(&mut rng);
            if q.is_zero() { Q::new(1, 2).unwrap() } else { q }
        })
        .collect();
    let r = Q::product(&xs);
    let exact = xs.iter().fold(rat_of(1, 1), |acc, q| acc * rat(*q));
    use malachite_base::num::arithmetic::traits::Abs;
    let err = (rat(r) - &exact).abs();
    let bound = rat_of(2 * 1000, 1) / rat_of(1, 1) * rat_of(1, 1i64 << 60);
    assert!(err <= bound, "V8 product bound violated: {err}");
}
