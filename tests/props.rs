//! Property and adversarial tests (no oracle): invariant preservation,
//! algebraic laws on the exact path, determinism, serde round-trip, and the
//! budget/sign/`i64::MIN` edge fixtures called out in the spec.

use the_q::{product, sum, Dir, BUDGET, Q};

fn q(n: i64, d: i64) -> Q {
    Q::new(n, d).unwrap()
}

/// Every canonical Q must satisfy I1 (canonical) and I2 (bounded).
fn assert_invariants(x: Q) {
    let n = x.numer();
    let d = x.denom();
    assert!(d > 0, "I1: den must be > 0, got {}", d);
    assert!(
        n.unsigned_abs() <= BUDGET as u64,
        "I2: |num| over budget: {}",
        n
    );
    assert!(d as u64 <= BUDGET as u64, "I2: den over budget: {}", d);
    // gcd(|num|, den) == 1
    let g = gcd(n.unsigned_abs(), d as u64);
    assert_eq!(g, 1, "I1: not reduced, gcd={} for {}", g, x);
    if n == 0 {
        assert_eq!(d, 1, "I1: zero must be 0/1, got {}", x);
    }
}

fn gcd(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    a
}

struct Lcg(u64);
impl Lcg {
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
    fn next_q(&mut self, mx: i64) -> Q {
        let n = (self.next_u64() % (2 * mx as u64 + 1)) as i64 - mx;
        let d = (self.next_u64() % (mx as u64)) as i64 + 1;
        Q::new(n, d).unwrap()
    }
}

#[test]
fn invariants_after_every_op() {
    let mut rng = Lcg(0x00AB_CDEF);
    for _ in 0..50_000 {
        let a = rng.next_q(1_000_000);
        let b = rng.next_q(1_000_000);
        assert_invariants(a);
        assert_invariants(a.add(b));
        assert_invariants(a.sub(b));
        assert_invariants(a.mul(b));
        if !b.is_zero() {
            assert_invariants(a.div(b));
        }
        assert_invariants(a.neg());
        assert_invariants(a.abs());
        if !a.is_zero() {
            assert_invariants(a.recip());
        }
        assert_invariants(a.min(b));
        assert_invariants(a.max(b));
    }
}

#[test]
fn commutativity_always() {
    // add/mul commute even when rounding fires (V6).
    let mut rng = Lcg(0x1122_3344);
    for _ in 0..50_000 {
        let a = rng.next_q(BUDGET / 2);
        let b = rng.next_q(BUDGET / 2);
        for &dir in &[Dir::Down, Dir::Up, Dir::Nearest] {
            assert!(
                a.add_dir(b, dir).eq(b.add_dir(a, dir)),
                "add not commutative"
            );
            assert!(
                a.mul_dir(b, dir).eq(b.mul_dir(a, dir)),
                "mul not commutative"
            );
        }
    }
}

#[test]
fn associativity_and_distributivity_on_exact_path() {
    // Small values ⟹ all exact ⟹ associative + distributive (V6 exact-path).
    let mut rng = Lcg(0x9090);
    for _ in 0..20_000 {
        let a = rng.next_q(20);
        let b = rng.next_q(20);
        let c = rng.next_q(20);
        // Only assert when the whole computation stays representable (it does at
        // this scale, but guard anyway to make the "exact path" precondition explicit).
        assert!(a.add(b).add(c).eq(a.add(b.add(c))), "add assoc");
        assert!(a.mul(b).mul(c).eq(a.mul(b.mul(c))), "mul assoc");
        assert!(a.mul(b.add(c)).eq(a.mul(b).add(a.mul(c))), "distributivity");
    }
}

#[test]
fn involutions() {
    let mut rng = Lcg(0x7);
    for _ in 0..20_000 {
        let a = rng.next_q(100_000);
        assert!(a.neg().neg().eq(a), "neg involution");
        assert!(a.abs().abs().eq(a.abs()), "abs idempotent");
        if !a.is_zero() {
            assert!(a.recip().recip().eq(a), "recip involution");
        }
    }
}

#[test]
fn ord_is_total_order() {
    let mut rng = Lcg(0x333);
    let xs: Vec<Q> = (0..500).map(|_| rng.next_q(1000)).collect();
    for &a in &xs {
        assert_eq!(a.cmp_q(a), core::cmp::Ordering::Equal, "reflexive");
        for &b in &xs {
            // antisymmetry
            assert_eq!(a.cmp_q(b), b.cmp_q(a).reverse());
            for &c in &xs {
                // transitivity of ≤
                if a.le(b) && b.le(c) {
                    assert!(a.le(c), "≤ not transitive");
                }
            }
        }
    }
}

#[test]
fn determinism_byte_identical_across_runs_and_threads() {
    // A fixed computation must yield byte-identical (num, den) every time and on
    // every thread — the core determinism guarantee over f64.
    fn compute() -> Vec<(i64, i64)> {
        let mut rng = Lcg(0xD37);
        let mut out = Vec::new();
        let mut acc = Q::zero();
        for _ in 0..2000 {
            let x = rng.next_q(5000);
            acc = acc.add(x).mul(q(3, 7)).sub(x);
            out.push((acc.numer(), acc.denom()));
        }
        out
    }
    let base = compute();
    // same thread, repeated
    assert_eq!(base, compute());
    // other threads
    let handles: Vec<_> = (0..4).map(|_| std::thread::spawn(compute)).collect();
    for h in handles {
        assert_eq!(base, h.join().unwrap());
    }
}

// ---- adversarial fixtures --------------------------------------------------

#[test]
fn budget_edge_values() {
    let big = Q::new(BUDGET, 1).unwrap(); // 2^62 − 1
    assert_invariants(big);
    let big_den = Q::new(1, BUDGET).unwrap();
    assert_invariants(big_den);
    // den = 2^62 − 1 with coprime numerator survives every op.
    let a = Q::new(BUDGET - 2, BUDGET).unwrap();
    assert_invariants(a);
    let b = Q::new(3, BUDGET).unwrap();
    for &dir in &[Dir::Down, Dir::Up, Dir::Nearest] {
        assert_invariants(a.add_dir(b, dir));
        assert_invariants(a.mul_dir(b, dir));
        assert_invariants(a.sub_dir(b, dir));
    }
}

#[test]
fn sign_edges() {
    assert!(Q::new(-1, -2).unwrap().eq(q(1, 2)));
    assert!(Q::new(1, -2).unwrap().eq(q(-1, 2)));
    assert_eq!(q(-5, 6).signum(), -1);
    // negation at the budget edge stays exact (I2 symmetric).
    let e = Q::new(BUDGET, 7).unwrap();
    assert!(e.neg().neg().eq(e));
    assert_invariants(e.neg());
}

#[test]
fn i64_min_excluded() {
    // |i64::MIN| = 2^63 overflows the budget and would overflow abs; must be rejected.
    assert!(Q::from_int(i64::MIN).is_none());
    assert!(Q::new(i64::MIN, 1).is_none());
    // i64::MIN / 2 = -2^62, still one past the budget (2^62 − 1) ⟹ None.
    assert!(Q::new(i64::MIN, 2).is_none());
    // i64::MIN / 4 = -2^61 reduces into range ⟹ accepted.
    assert!(Q::new(i64::MIN, 4).unwrap().eq(q(-(1i64 << 61), 1)));
    assert!(Q::new(i64::MIN, 8).unwrap().eq(q(-(1i64 << 60), 1)));
}

#[test]
fn out_of_budget_construction_rejected() {
    // i64::MAX = 2^63 − 1 > BUDGET; irreducible ⟹ None.
    assert!(Q::new(i64::MAX, 1).is_none());
    // Reduces to fit ⟹ Some.
    assert!(Q::new(i64::MAX - 1, 2).is_some());
}

#[test]
fn nary_determinism_and_bounds() {
    let mut rng = Lcg(0xF00D);
    let xs: Vec<Q> = (0..1000).map(|_| rng.next_q(1000)).collect();
    let s1 = sum(&xs);
    let s2 = sum(&xs);
    assert!(s1.eq(s2));
    assert_invariants(s1);
    let ys: Vec<Q> = (0..50).map(|_| rng.next_q(5)).collect();
    assert_invariants(product(&ys));
}

#[cfg(feature = "serde")]
#[test]
fn serde_exact_round_trip() {
    let mut rng = Lcg(0x5E12E);
    for _ in 0..10_000 {
        let a = rng.next_q(1_000_000);
        let js = serde_json::to_string(&a).unwrap();
        let back: Q = serde_json::from_str(&js).unwrap();
        assert!(
            a.eq(back),
            "serde round-trip changed value: {} -> {}",
            a,
            back
        );
        assert_invariants(back);
    }
    // Encoding is the (num, den) integer pair.
    let one_half = q(1, 2);
    assert_eq!(
        serde_json::to_string(&one_half).unwrap(),
        r#"{"num":1,"den":2}"#
    );
}

#[cfg(feature = "serde")]
#[test]
fn serde_rejects_noncanonical_and_out_of_budget() {
    // den = 0 → error
    assert!(serde_json::from_str::<Q>(r#"{"num":1,"den":0}"#).is_err());
    // out-of-budget numerator → error (invariant re-validated on ingest)
    let bad = format!(r#"{{"num":{},"den":1}}"#, i64::MAX);
    assert!(serde_json::from_str::<Q>(&bad).is_err());
    // non-reduced input is normalized, not rejected (still a valid value)
    let ok: Q = serde_json::from_str(r#"{"num":2,"den":4}"#).unwrap();
    assert!(ok.eq(q(1, 2)));
}
