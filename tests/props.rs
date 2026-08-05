//! Property tests. These check the invariants and laws the crate claims, at
//! runtime.
//!
//! These tests overlap with the Verus obligations. The overlap gives a runtime
//! check of each proved claim. It applies in particular to determinism,
//! commutativity and serde round-tripping. The consuming engine depends on
//! these three claims.

#![allow(clippy::unusual_byte_groupings)]

mod common;

use common::*;
use the_q::{Dir, Rat};

// ---------------------------------------------------------------------------
// The type invariant
// ---------------------------------------------------------------------------

#[test]
fn every_operation_preserves_the_invariant() {
    let mut rng = Rng::new(0x1_0000_0001);
    for _ in 0..30_000 {
        let (a, b) = (rng.q(), rng.q());
        for dir in DIRS {
            assert_wf(Rat::add_dir(a, b, dir), "add");
            assert_wf(Rat::sub_dir(a, b, dir), "sub");
            assert_wf(Rat::mul_dir(a, b, dir), "mul");
            if !b.is_zero() {
                assert_wf(Rat::div_dir(a, b, dir), "div");
            }
        }
        assert_wf(a.neg(), "neg");
        assert_wf(a.abs(), "abs");
        if !a.is_zero() {
            assert_wf(a.recip(), "recip");
        }
        assert_wf(Rat::min(a, b), "min");
        assert_wf(Rat::max(a, b), "max");
        let (lo, hi) = if Rat::le(a, b) { (a, b) } else { (b, a) };
        assert_wf(Rat::clamp(rng.q(), lo, hi), "clamp");
    }
}

// ---------------------------------------------------------------------------
// Commutativity. The crate claims it unconditionally, including under rounding.
// ---------------------------------------------------------------------------

#[test]
fn add_and_mul_are_commutative_bit_for_bit() {
    let mut rng = Rng::new(0xC0_11);
    for _ in 0..50_000 {
        let (a, b) = (rng.q(), rng.q());
        for dir in DIRS {
            assert_eq!(
                Rat::add_dir(a, b, dir),
                Rat::add_dir(b, a, dir),
                "add is not commutative at {a}, {b}, {dir:?}"
            );
            assert_eq!(
                Rat::mul_dir(a, b, dir),
                Rat::mul_dir(b, a, dir),
                "mul is not commutative at {a}, {b}, {dir:?}"
            );
        }
    }
}

#[test]
fn associativity_holds_on_the_exact_path() {
    // The crate claims associativity *only* when nothing rounds. This test uses
    // inputs small enough that no operation can round.
    let mut rng = Rng::new(0xA550C);
    for _ in 0..20_000 {
        let small =
            |r: &mut Rng| Rat::new(r.below(2001) as i64 - 1000, r.below(1000) as i64 + 1).unwrap();
        let (a, b, c) = (small(&mut rng), small(&mut rng), small(&mut rng));
        let lhs = Rat::add(Rat::add(a, b), c);
        let rhs = Rat::add(a, Rat::add(b, c));
        assert_eq!(lhs, rhs, "add not associative on small values");
        let lhs = Rat::mul(Rat::mul(a, b), c);
        let rhs = Rat::mul(a, Rat::mul(b, c));
        assert_eq!(lhs, rhs, "mul not associative on small values");
        // Distributivity holds on the same inputs.
        let lhs = Rat::mul(a, Rat::add(b, c));
        let rhs = Rat::add(Rat::mul(a, b), Rat::mul(a, c));
        assert_eq!(lhs, rhs, "distributivity fails on small values");
    }
}

// ---------------------------------------------------------------------------
// Order
// ---------------------------------------------------------------------------

#[test]
fn ord_is_a_total_order_agreeing_with_the_value_order() {
    let mut rng = Rng::new(0x0_D3_12);
    for _ in 0..20_000 {
        let (a, b, c) = (rng.q(), rng.q(), rng.q());
        // Reflexive, antisymmetric, transitive, total.
        assert!(Rat::le(a, a));
        assert!(Rat::le(a, b) || Rat::le(b, a));
        if Rat::le(a, b) && Rat::le(b, a) {
            assert_eq!(a, b, "antisymmetry: {a} and {b} compare equal but differ");
        }
        if Rat::le(a, b) && Rat::le(b, c) {
            assert!(Rat::le(a, c), "transitivity failed on {a}, {b}, {c}");
        }
        // The order agrees with the oracle order and with `Ord`.
        assert_eq!(Rat::le(a, b), rat(a) <= rat(b));
        assert_eq!(a.cmp(&b), rat(a).cmp(&rat(b)));
        assert_eq!(
            a == b,
            rat(a) == rat(b),
            "canonicality: eq must be value eq"
        );
        // min/max/clamp agree with the order.
        assert_eq!(Rat::min(a, b), if Rat::le(a, b) { a } else { b });
        assert_eq!(Rat::max(a, b), if Rat::le(a, b) { b } else { a });
        let (lo, hi) = if Rat::le(a, b) { (a, b) } else { (b, a) };
        let cl = Rat::clamp(c, lo, hi);
        assert!(Rat::le(lo, cl) && Rat::le(cl, hi));
    }
}

#[test]
fn hash_agrees_with_eq() {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};
    let h = |q: Rat| {
        let mut s = DefaultHasher::new();
        q.hash(&mut s);
        s.finish()
    };
    // Canonicality makes equal values structurally identical. Therefore equal
    // values hash identically. 6/8 *is* 3/4, and is not merely equal to it.
    assert_eq!(Rat::new(6, 8).unwrap(), Rat::new(3, 4).unwrap());
    assert_eq!(h(Rat::new(6, 8).unwrap()), h(Rat::new(3, 4).unwrap()));
    assert_eq!(Rat::new(-2, -4).unwrap(), Rat::new(1, 2).unwrap());
    assert_eq!(h(Rat::new(2, -4).unwrap()), h(Rat::new(-1, 2).unwrap()));
    assert_eq!(h(Rat::new(0, 5).unwrap()), h(Rat::zero()));
}

// ---------------------------------------------------------------------------
// R1 on constructed-representable cases
// ---------------------------------------------------------------------------

#[test]
fn short_decimals_are_exact_end_to_end() {
    // The engine's ingestion path supplies reliabilities and weights as
    // decimals with 4 or fewer places. All operations on them stay exact.
    let mut rng = Rng::new(0xDEC1_1A1);
    for _ in 0..20_000 {
        let a = Rat::from_decimal(rng.below(20001) as i64 - 10000, 4).unwrap();
        let b = Rat::from_decimal(rng.below(20001) as i64 - 10000, 4).unwrap();
        assert_eq!(rat(Rat::add(a, b)), rat(a) + rat(b));
        assert_eq!(rat(Rat::sub(a, b)), rat(a) - rat(b));
        assert_eq!(rat(Rat::mul(a, b)), rat(a) * rat(b));
        if !b.is_zero() {
            assert_eq!(rat(Rat::div(a, b)), rat(a) / rat(b));
        }
    }
    assert_eq!(Rat::from_decimal(85, 2).unwrap(), Rat::new(17, 20).unwrap());
    assert_eq!(
        Rat::from_decimal(-125, 3).unwrap(),
        Rat::new(-1, 8).unwrap()
    );
    assert_eq!(Rat::from_decimal(0, 4).unwrap(), Rat::zero());
}

#[test]
fn identities_and_involutions() {
    let mut rng = Rng::new(0x1D3_7);
    for _ in 0..20_000 {
        let a = rng.q();
        assert_eq!(Rat::add(a, Rat::zero()), a);
        assert_eq!(Rat::mul(a, Rat::one()), a);
        assert_eq!(Rat::mul(a, Rat::zero()), Rat::zero());
        assert_eq!(Rat::sub(a, a), Rat::zero());
        assert_eq!(a.neg().neg(), a);
        assert_eq!(a.abs().abs(), a.abs());
        assert_eq!(a.neg().abs(), a.abs());
        if !a.is_zero() {
            assert_eq!(a.recip().recip(), a);
            assert_eq!(Rat::div(a, a), Rat::one());
            assert_eq!(Rat::mul(a, a.recip()), Rat::one());
        }
        assert_eq!(Rat::sub(Rat::zero(), a), a.neg());
    }
}

// ---------------------------------------------------------------------------
// Determinism
// ---------------------------------------------------------------------------

#[test]
fn results_are_byte_identical_across_runs_and_threads() {
    fn workload(seed: u64) -> Vec<(i64, i64)> {
        let mut rng = Rng::new(seed);
        let mut acc = Rat::from_decimal(1, 1).unwrap();
        let mut out = Vec::with_capacity(2000);
        for i in 0..2000 {
            let x = rng.q_unit();
            acc = match i % 4 {
                0 => Rat::add(acc, x),
                1 => Rat::mul(acc, x),
                2 => Rat::sub(acc, x),
                _ => {
                    if x.is_zero() {
                        acc
                    } else {
                        Rat::div(acc, x)
                    }
                }
            };
            out.push((acc.numerator(), acc.denominator()));
        }
        out
    }

    let baseline = workload(0x5EED);
    // The same workload runs again in the same process.
    assert_eq!(baseline, workload(0x5EED));
    // The same workload runs concurrently on other threads.
    let handles: Vec<_> = (0..8)
        .map(|_| std::thread::spawn(|| workload(0x5EED)))
        .collect();
    for h in handles {
        assert_eq!(
            baseline,
            h.join().unwrap(),
            "results differ across threads — determinism is broken"
        );
    }
}

// ---------------------------------------------------------------------------
// Display and serde
// ---------------------------------------------------------------------------

#[test]
fn display_is_canonical() {
    assert_eq!(Rat::new(6, 8).unwrap().to_string(), "3/4");
    assert_eq!(Rat::new(2, -4).unwrap().to_string(), "-1/2");
    assert_eq!(Rat::zero().to_string(), "0/1");
    assert_eq!(Rat::from_decimal(85, 2).unwrap().to_string(), "17/20");
}

#[cfg(feature = "serde")]
#[test]
fn serde_round_trips_exactly() {
    let mut rng = Rng::new(0x5E12DE);
    for _ in 0..20_000 {
        let a = rng.q();
        let s = serde_json::to_string(&a).unwrap();
        let back: Rat = serde_json::from_str(&s).unwrap();
        assert_eq!(a, back, "serde round-trip changed {a} (encoded as {s})");
    }
    // The encoding is the integer pair. It is not a float.
    assert_eq!(
        serde_json::to_string(&Rat::new(17, 20).unwrap()).unwrap(),
        "[17,20]"
    );
    // Deserialization rejects a non-canonical or out-of-budget payload. It does
    // not convert such a payload into a value that violates the invariant.
    assert!(serde_json::from_str::<Rat>("[1,0]").is_err());
    assert!(serde_json::from_str::<Rat>("[9223372036854775807,1]").is_err());
    // Deserialization accepts a non-reduced payload and canonicalises it.
    let q: Rat = serde_json::from_str("[6,8]").unwrap();
    assert_eq!(q, Rat::new(3, 4).unwrap());
}

// ---------------------------------------------------------------------------
// N-ary helpers
// ---------------------------------------------------------------------------

#[test]
fn nary_helpers_are_left_folds() {
    let mut rng = Rng::new(0x4A12_0);
    for _ in 0..2_000 {
        let n = (rng.below(8) + 1) as usize;
        let xs: Vec<Rat> = (0..n).map(|_| rng.q_unit()).collect();

        let mut expect = Rat::zero();
        for &x in &xs {
            expect = Rat::add(expect, x);
        }
        assert_eq!(the_q::nary::sum(&xs), expect);

        let mut expect = Rat::one();
        for &x in &xs {
            expect = Rat::mul(expect, x);
        }
        assert_eq!(the_q::nary::product(&xs), expect);
    }
    assert_eq!(the_q::nary::sum(&[]), Rat::zero());
    assert_eq!(the_q::nary::product(&[]), Rat::one());
}

#[test]
fn weighted_mean_matches_its_definition() {
    let mut rng = Rng::new(0x3EA9_0);
    for _ in 0..2_000 {
        let n = (rng.below(6) + 1) as usize;
        let pairs: Vec<(Rat, Rat)> = (0..n).map(|_| (rng.q_unit(), rng.q_unit())).collect();
        let got = the_q::nary::weighted_mean(&pairs);
        let mut num = Rat::zero();
        let mut den = Rat::zero();
        for &(w, x) in &pairs {
            num = Rat::add(num, Rat::mul(w, x));
            den = Rat::add(den, w);
        }
        if den.is_zero() {
            assert!(got.is_none());
        } else {
            assert_eq!(got.unwrap(), Rat::div(num, den));
        }
    }
    // A zero total weight has no mean. The crate returns `None` for this case.
    assert!(the_q::nary::weighted_mean(&[(Rat::zero(), Rat::one())]).is_none());
    assert!(the_q::nary::weighted_mean(&[]).is_none());
}

// ---------------------------------------------------------------------------
// Intervals
// ---------------------------------------------------------------------------

#[test]
fn intervals_bracket_the_exact_result() {
    use the_q::interval::QI;
    let mut rng = Rng::new(0x1_7_7_0);
    for _ in 0..10_000 {
        let (a, b) = (rng.q_unit(), rng.q_unit());
        let ia = QI::exact(a);
        let ib = QI::exact(b);
        let s = QI::add(ia, ib);
        let exact = rat(a) + rat(b);
        assert!(
            rat(s.lo) <= exact && exact <= rat(s.hi),
            "sum interval misses {exact}"
        );
        let d = QI::sub(ia, ib);
        let exact = rat(a) - rat(b);
        assert!(
            rat(d.lo) <= exact && exact <= rat(d.hi),
            "diff interval misses {exact}"
        );
        let m = QI::mul(ia, ib);
        let exact = rat(a) * rat(b);
        assert!(
            rat(m.lo) <= exact && exact <= rat(m.hi),
            "product interval misses {exact}"
        );
        // On the exact path, the interval collapses to a point.
        if rat(s.lo) == rat(s.hi) {
            assert!(QI::add(ia, ib).width().is_zero());
        }
    }
}

#[test]
fn interval_width_is_zero_on_the_exact_path() {
    use the_q::interval::QI;
    let a = QI::exact(Rat::from_decimal(85, 2).unwrap());
    let b = QI::exact(Rat::from_decimal(15, 2).unwrap());
    assert!(QI::add(a, b).width().is_zero());
    assert!(QI::mul(a, b).width().is_zero());
    assert_eq!(QI::add(a, b).lo, Rat::one());
}

/// Non-degenerate, arbitrary-sign intervals bracket the exact result of every
/// point drawn from inside them. `intervals_bracket_the_exact_result` covers
/// only the endpoint-to-endpoint case. This test is the black-box counterpart
/// of `theorem_interval_add_contains`, `_sub_contains` and `_mul_contains`.
/// Those theorems hold for arbitrary `x` and `y` in range. This test samples
/// that range, and does not use only the endpoints. A point interval can
/// exercise the endpoints alone. Signed endpoints exercise `mul`'s corner rule
/// across every sign pattern. The nonnegative-only test above does not reach
/// those sign patterns.
#[test]
fn signed_intervals_bracket_arbitrary_interior_points() {
    use the_q::interval::QI;
    let mut rng = Rng::new(0x519_5460_51_9);
    for _ in 0..10_000 {
        let (a_lo, a_hi) = ordered_pair(&mut rng);
        let (b_lo, b_hi) = ordered_pair(&mut rng);
        let ia = QI::new(a_lo, a_hi);
        let ib = QI::new(b_lo, b_hi);
        let x = interior_point(&mut rng, a_lo, a_hi);
        let y = interior_point(&mut rng, b_lo, b_hi);

        let s = QI::add(ia, ib);
        assert!(Rat::le(s.lo, s.hi), "sum interval not well-formed");
        let exact = rat(x) + rat(y);
        assert!(
            rat(s.lo) <= exact && exact <= rat(s.hi),
            "sum interval [{},{}] misses {exact} (x={x:?}, y={y:?})",
            rat(s.lo),
            rat(s.hi)
        );

        let d = QI::sub(ia, ib);
        assert!(Rat::le(d.lo, d.hi), "difference interval not well-formed");
        let exact = rat(x) - rat(y);
        assert!(
            rat(d.lo) <= exact && exact <= rat(d.hi),
            "diff interval [{},{}] misses {exact} (x={x:?}, y={y:?})",
            rat(d.lo),
            rat(d.hi)
        );

        let m = QI::mul(ia, ib);
        assert!(Rat::le(m.lo, m.hi), "product interval not well-formed");
        let exact = rat(x) * rat(y);
        assert!(
            rat(m.lo) <= exact && exact <= rat(m.hi),
            "product interval [{},{}] misses {exact} (x={x:?}, y={y:?})",
            rat(m.lo),
            rat(m.hi)
        );
    }
}

/// The interval layer composes. The output of one interval operation feeds
/// straight into the next, with no re-validation in between. The result stays
/// well-formed and keeps bracketing the exact chained result. Signed endpoints
/// exercise `mul`'s corner rule inside the chain.
#[test]
fn interval_ops_chain_without_reestablishing_wf() {
    use the_q::interval::QI;
    let mut rng = Rng::new(0xC0FFEE_5EED);
    for _ in 0..5_000 {
        let (a_lo, a_hi) = ordered_pair(&mut rng);
        let (b_lo, b_hi) = ordered_pair(&mut rng);
        let (c_lo, c_hi) = ordered_pair(&mut rng);
        let ia = QI::new(a_lo, a_hi);
        let ib = QI::new(b_lo, b_hi);
        let ic = QI::new(c_lo, c_hi);

        // `QI::add`'s result feeds `QI::mul` directly. That result feeds
        // `QI::sub` directly. There is no intermediate `QI::new` or re-check.
        let sum = QI::add(ia, ib);
        let prod = QI::mul(sum, ic);
        let diff = QI::sub(prod, ia);
        assert!(
            Rat::le(diff.lo, diff.hi),
            "chained interval lost well-formedness"
        );

        let x = interior_point(&mut rng, a_lo, a_hi);
        let y = interior_point(&mut rng, b_lo, b_hi);
        let z = interior_point(&mut rng, c_lo, c_hi);
        let exact = (rat(x) + rat(y)) * rat(z) - rat(x);
        assert!(
            rat(diff.lo) <= exact && exact <= rat(diff.hi),
            "chained interval [{},{}] misses {exact}",
            rat(diff.lo),
            rat(diff.hi)
        );
    }
}

/// Returns a pair `(lo, hi)` with `lo <= hi`. The pair comes from the same
/// mixture of magnitude classes as `Rng::q`. The values are signed. Therefore
/// both endpoints can land on either side of zero.
fn ordered_pair(rng: &mut Rng) -> (Rat, Rat) {
    let (p, q) = (rng.q(), rng.q());
    if Rat::le(p, q) {
        (p, q)
    } else {
        (q, p)
    }
}

/// Returns a `Rat` in `[lo, hi]`. The distribution is biased toward the
/// endpoints. Therefore the corner rule's boundary gets as much coverage as its
/// interior.
fn interior_point(rng: &mut Rng, lo: Rat, hi: Rat) -> Rat {
    match rng.below(4) {
        0 => lo,
        1 => hi,
        _ => Rat::clamp(rng.q(), lo, hi),
    }
}

// ---------------------------------------------------------------------------
// pow
// ---------------------------------------------------------------------------

#[test]
fn pow_is_repeated_multiplication() {
    let mut rng = Rng::new(0x0_0_0_1);
    for _ in 0..2_000 {
        let a = rng.q_unit();
        let e = rng.below(8) as u32;
        let mut expect = Rat::one();
        for _ in 0..e {
            expect = Rat::mul(expect, a);
        }
        assert_eq!(a.pow_u32(e), expect);
    }
    assert_eq!(Rat::new(2, 3).unwrap().pow_u32(0), Rat::one());
    assert_eq!(Rat::new(2, 3).unwrap().pow_u32(3), Rat::new(8, 27).unwrap());
}

// ---------------------------------------------------------------------------
// The directed modes are directed
// ---------------------------------------------------------------------------

#[test]
fn down_never_exceeds_up() {
    let mut rng = Rng::new(0xD1AC);
    for _ in 0..30_000 {
        let (a, b) = (rng.q(), rng.q());
        for (lo, hi, mid) in [
            (
                Rat::add_dir(a, b, Dir::Down),
                Rat::add_dir(a, b, Dir::Up),
                Rat::add_dir(a, b, Dir::Nearest),
            ),
            (
                Rat::mul_dir(a, b, Dir::Down),
                Rat::mul_dir(a, b, Dir::Up),
                Rat::mul_dir(a, b, Dir::Nearest),
            ),
        ] {
            assert!(Rat::le(lo, hi), "Down > Up for {a}, {b}");
            assert!(
                Rat::le(lo, mid) && Rat::le(mid, hi),
                "Nearest outside [Down, Up]"
            );
        }
    }
}
