//! Property tests: the invariants and laws the crate claims, checked at runtime.
//!
//! These overlap deliberately with the Verus obligations. A proof that has not
//! been run is a hypothesis, and a proof that has been run is still worth
//! double-checking against reality — especially the claims (determinism,
//! commutativity, serde round-tripping) that the consuming engine will lean on.

#![allow(clippy::unusual_byte_groupings)]

mod common;

use common::*;
use the_q::{Dir, Q};

// ---------------------------------------------------------------------------
// The type invariant
// ---------------------------------------------------------------------------

#[test]
fn every_operation_preserves_the_invariant() {
    let mut rng = Rng::new(0x1_0000_0001);
    for _ in 0..30_000 {
        let (a, b) = (rng.q(), rng.q());
        for dir in DIRS {
            assert_wf(Q::add_dir(a, b, dir), "add");
            assert_wf(Q::sub_dir(a, b, dir), "sub");
            assert_wf(Q::mul_dir(a, b, dir), "mul");
            if !b.is_zero() {
                assert_wf(Q::div_dir(a, b, dir), "div");
            }
        }
        assert_wf(a.neg(), "neg");
        assert_wf(a.abs(), "abs");
        if !a.is_zero() {
            assert_wf(a.recip(), "recip");
        }
        assert_wf(Q::min(a, b), "min");
        assert_wf(Q::max(a, b), "max");
        let (lo, hi) = if Q::le(a, b) { (a, b) } else { (b, a) };
        assert_wf(Q::clamp(rng.q(), lo, hi), "clamp");
    }
}

// ---------------------------------------------------------------------------
// Commutativity — claimed unconditionally, rounding and all
// ---------------------------------------------------------------------------

#[test]
fn add_and_mul_are_commutative_bit_for_bit() {
    let mut rng = Rng::new(0xC0_11);
    for _ in 0..50_000 {
        let (a, b) = (rng.q(), rng.q());
        for dir in DIRS {
            assert_eq!(
                Q::add_dir(a, b, dir),
                Q::add_dir(b, a, dir),
                "add is not commutative at {a}, {b}, {dir:?}"
            );
            assert_eq!(
                Q::mul_dir(a, b, dir),
                Q::mul_dir(b, a, dir),
                "mul is not commutative at {a}, {b}, {dir:?}"
            );
        }
    }
}

#[test]
fn associativity_holds_on_the_exact_path() {
    // The crate claims associativity *only* when nothing rounds. Verify the
    // claim on inputs small enough that nothing can round.
    let mut rng = Rng::new(0xA550C);
    for _ in 0..20_000 {
        let small =
            |r: &mut Rng| Q::new(r.below(2001) as i64 - 1000, r.below(1000) as i64 + 1).unwrap();
        let (a, b, c) = (small(&mut rng), small(&mut rng), small(&mut rng));
        let lhs = Q::add(Q::add(a, b), c);
        let rhs = Q::add(a, Q::add(b, c));
        assert_eq!(lhs, rhs, "add not associative on small values");
        let lhs = Q::mul(Q::mul(a, b), c);
        let rhs = Q::mul(a, Q::mul(b, c));
        assert_eq!(lhs, rhs, "mul not associative on small values");
        // Distributivity too.
        let lhs = Q::mul(a, Q::add(b, c));
        let rhs = Q::add(Q::mul(a, b), Q::mul(a, c));
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
        assert!(Q::le(a, a));
        assert!(Q::le(a, b) || Q::le(b, a));
        if Q::le(a, b) && Q::le(b, a) {
            assert_eq!(a, b, "antisymmetry: {a} and {b} compare equal but differ");
        }
        if Q::le(a, b) && Q::le(b, c) {
            assert!(Q::le(a, c), "transitivity failed on {a}, {b}, {c}");
        }
        // Agreement with the oracle order and with `Ord`.
        assert_eq!(Q::le(a, b), rat(a) <= rat(b));
        assert_eq!(a.cmp(&b), rat(a).cmp(&rat(b)));
        assert_eq!(
            a == b,
            rat(a) == rat(b),
            "canonicality: eq must be value eq"
        );
        // min/max/clamp agree with the order.
        assert_eq!(Q::min(a, b), if Q::le(a, b) { a } else { b });
        assert_eq!(Q::max(a, b), if Q::le(a, b) { b } else { a });
        let (lo, hi) = if Q::le(a, b) { (a, b) } else { (b, a) };
        let cl = Q::clamp(c, lo, hi);
        assert!(Q::le(lo, cl) && Q::le(cl, hi));
    }
}

#[test]
fn hash_agrees_with_eq() {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};
    let h = |q: Q| {
        let mut s = DefaultHasher::new();
        q.hash(&mut s);
        s.finish()
    };
    // Canonicality means equal values are structurally identical, so equal
    // values must hash identically — and 6/8 must *be* 3/4, not merely equal.
    assert_eq!(Q::new(6, 8).unwrap(), Q::new(3, 4).unwrap());
    assert_eq!(h(Q::new(6, 8).unwrap()), h(Q::new(3, 4).unwrap()));
    assert_eq!(Q::new(-2, -4).unwrap(), Q::new(1, 2).unwrap());
    assert_eq!(h(Q::new(2, -4).unwrap()), h(Q::new(-1, 2).unwrap()));
    assert_eq!(h(Q::new(0, 5).unwrap()), h(Q::zero()));
}

// ---------------------------------------------------------------------------
// R1 on constructed-representable cases
// ---------------------------------------------------------------------------

#[test]
fn short_decimals_are_exact_end_to_end() {
    // The engine's ingestion path: reliabilities and weights as <= 4-place
    // decimals. Everything about them should be exact, all the way through.
    let mut rng = Rng::new(0xDEC1_1A1);
    for _ in 0..20_000 {
        let a = Q::from_decimal(rng.below(20001) as i64 - 10000, 4).unwrap();
        let b = Q::from_decimal(rng.below(20001) as i64 - 10000, 4).unwrap();
        assert_eq!(rat(Q::add(a, b)), rat(a) + rat(b));
        assert_eq!(rat(Q::sub(a, b)), rat(a) - rat(b));
        assert_eq!(rat(Q::mul(a, b)), rat(a) * rat(b));
        if !b.is_zero() {
            assert_eq!(rat(Q::div(a, b)), rat(a) / rat(b));
        }
    }
    assert_eq!(Q::from_decimal(85, 2).unwrap(), Q::new(17, 20).unwrap());
    assert_eq!(Q::from_decimal(-125, 3).unwrap(), Q::new(-1, 8).unwrap());
    assert_eq!(Q::from_decimal(0, 4).unwrap(), Q::zero());
}

#[test]
fn identities_and_involutions() {
    let mut rng = Rng::new(0x1D3_7);
    for _ in 0..20_000 {
        let a = rng.q();
        assert_eq!(Q::add(a, Q::zero()), a);
        assert_eq!(Q::mul(a, Q::one()), a);
        assert_eq!(Q::mul(a, Q::zero()), Q::zero());
        assert_eq!(Q::sub(a, a), Q::zero());
        assert_eq!(a.neg().neg(), a);
        assert_eq!(a.abs().abs(), a.abs());
        assert_eq!(a.neg().abs(), a.abs());
        if !a.is_zero() {
            assert_eq!(a.recip().recip(), a);
            assert_eq!(Q::div(a, a), Q::one());
            assert_eq!(Q::mul(a, a.recip()), Q::one());
        }
        assert_eq!(Q::sub(Q::zero(), a), a.neg());
    }
}

// ---------------------------------------------------------------------------
// Determinism
// ---------------------------------------------------------------------------

#[test]
fn results_are_byte_identical_across_runs_and_threads() {
    fn workload(seed: u64) -> Vec<(i64, i64)> {
        let mut rng = Rng::new(seed);
        let mut acc = Q::from_decimal(1, 1).unwrap();
        let mut out = Vec::with_capacity(2000);
        for i in 0..2000 {
            let x = rng.q_unit();
            acc = match i % 4 {
                0 => Q::add(acc, x),
                1 => Q::mul(acc, x),
                2 => Q::sub(acc, x),
                _ => {
                    if x.is_zero() {
                        acc
                    } else {
                        Q::div(acc, x)
                    }
                }
            };
            out.push((acc.numerator(), acc.denominator()));
        }
        out
    }

    let baseline = workload(0x5EED);
    // Same run, again.
    assert_eq!(baseline, workload(0x5EED));
    // Concurrently, on other threads.
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
    assert_eq!(Q::new(6, 8).unwrap().to_string(), "3/4");
    assert_eq!(Q::new(2, -4).unwrap().to_string(), "-1/2");
    assert_eq!(Q::zero().to_string(), "0/1");
    assert_eq!(Q::from_decimal(85, 2).unwrap().to_string(), "17/20");
}

#[cfg(feature = "serde")]
#[test]
fn serde_round_trips_exactly() {
    let mut rng = Rng::new(0x5E12DE);
    for _ in 0..20_000 {
        let a = rng.q();
        let s = serde_json::to_string(&a).unwrap();
        let back: Q = serde_json::from_str(&s).unwrap();
        assert_eq!(a, back, "serde round-trip changed {a} (encoded as {s})");
    }
    // The encoding is the integer pair, not a float.
    assert_eq!(
        serde_json::to_string(&Q::new(17, 20).unwrap()).unwrap(),
        "[17,20]"
    );
    // A non-canonical or out-of-budget payload is rejected, not silently fixed
    // into an invariant-violating value.
    assert!(serde_json::from_str::<Q>("[1,0]").is_err());
    assert!(serde_json::from_str::<Q>("[9223372036854775807,1]").is_err());
    // A non-reduced payload is accepted and canonicalised.
    let q: Q = serde_json::from_str("[6,8]").unwrap();
    assert_eq!(q, Q::new(3, 4).unwrap());
}

// ---------------------------------------------------------------------------
// N-ary helpers
// ---------------------------------------------------------------------------

#[test]
fn nary_helpers_are_left_folds() {
    let mut rng = Rng::new(0x4A12_0);
    for _ in 0..2_000 {
        let n = (rng.below(8) + 1) as usize;
        let xs: Vec<Q> = (0..n).map(|_| rng.q_unit()).collect();

        let mut expect = Q::zero();
        for &x in &xs {
            expect = Q::add(expect, x);
        }
        assert_eq!(the_q::nary::sum(&xs), expect);

        let mut expect = Q::one();
        for &x in &xs {
            expect = Q::mul(expect, x);
        }
        assert_eq!(the_q::nary::product(&xs), expect);
    }
    assert_eq!(the_q::nary::sum(&[]), Q::zero());
    assert_eq!(the_q::nary::product(&[]), Q::one());
}

#[test]
fn weighted_mean_matches_its_definition() {
    let mut rng = Rng::new(0x3EA9_0);
    for _ in 0..2_000 {
        let n = (rng.below(6) + 1) as usize;
        let pairs: Vec<(Q, Q)> = (0..n).map(|_| (rng.q_unit(), rng.q_unit())).collect();
        let got = the_q::nary::weighted_mean(&pairs);
        let mut num = Q::zero();
        let mut den = Q::zero();
        for &(w, x) in &pairs {
            num = Q::add(num, Q::mul(w, x));
            den = Q::add(den, w);
        }
        if den.is_zero() {
            assert!(got.is_none());
        } else {
            assert_eq!(got.unwrap(), Q::div(num, den));
        }
    }
    // Zero total weight has no mean, and the crate says so rather than
    // inventing one.
    assert!(the_q::nary::weighted_mean(&[(Q::zero(), Q::one())]).is_none());
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
        // On the exact path the interval collapses to a point.
        if rat(s.lo) == rat(s.hi) {
            assert!(QI::add(ia, ib).width().is_zero());
        }
    }
}

#[test]
fn interval_width_is_zero_on_the_exact_path() {
    use the_q::interval::QI;
    let a = QI::exact(Q::from_decimal(85, 2).unwrap());
    let b = QI::exact(Q::from_decimal(15, 2).unwrap());
    assert!(QI::add(a, b).width().is_zero());
    assert!(QI::mul(a, b).width().is_zero());
    assert_eq!(QI::add(a, b).lo, Q::one());
}

/// Non-degenerate, arbitrary-sign intervals bracket the exact result of every
/// point drawn from inside them — not just the endpoint-to-endpoint case
/// `intervals_bracket_the_exact_result` checks. This is the black-box
/// counterpart of `theorem_interval_add_contains`, `_sub_contains` and
/// `_mul_contains`: those are proved for arbitrary `x`/`y` in range, and this
/// samples that arbitrary range instead of only ever using the endpoints
/// themselves (which is all a point interval can exercise). Signed endpoints
/// in particular exercise `mul`'s corner rule across every sign pattern,
/// which the existing (nonnegative-only) test above never reaches.
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
        assert!(Q::le(s.lo, s.hi), "sum interval not well-formed");
        let exact = rat(x) + rat(y);
        assert!(
            rat(s.lo) <= exact && exact <= rat(s.hi),
            "sum interval [{},{}] misses {exact} (x={x:?}, y={y:?})",
            rat(s.lo),
            rat(s.hi)
        );

        let d = QI::sub(ia, ib);
        assert!(Q::le(d.lo, d.hi), "difference interval not well-formed");
        let exact = rat(x) - rat(y);
        assert!(
            rat(d.lo) <= exact && exact <= rat(d.hi),
            "diff interval [{},{}] misses {exact} (x={x:?}, y={y:?})",
            rat(d.lo),
            rat(d.hi)
        );

        let m = QI::mul(ia, ib);
        assert!(Q::le(m.lo, m.hi), "product interval not well-formed");
        let exact = rat(x) * rat(y);
        assert!(
            rat(m.lo) <= exact && exact <= rat(m.hi),
            "product interval [{},{}] misses {exact} (x={x:?}, y={y:?})",
            rat(m.lo),
            rat(m.hi)
        );
    }
}

/// The composability the layer is supposed to have: the output of one
/// interval operation, fed straight into the next without any re-validation
/// in between, stays well-formed and keeps bracketing the exact chained
/// result. Signed endpoints exercise `mul`'s corner rule inside the chain.
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

        // `QI::add`'s result feeds `QI::mul` directly, and that result feeds
        // `QI::sub` directly: no intermediate `QI::new`/re-check.
        let sum = QI::add(ia, ib);
        let prod = QI::mul(sum, ic);
        let diff = QI::sub(prod, ia);
        assert!(
            Q::le(diff.lo, diff.hi),
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

/// A uniformly-flavoured pair `(lo, hi)` with `lo <= hi`, drawn from the same
/// mixture of magnitude classes as `Rng::q` — signed, so both endpoints can
/// land on either side of zero.
fn ordered_pair(rng: &mut Rng) -> (Q, Q) {
    let (p, q) = (rng.q(), rng.q());
    if Q::le(p, q) {
        (p, q)
    } else {
        (q, p)
    }
}

/// A `Q` in `[lo, hi]`, biased toward the endpoints themselves so the corner
/// rule's boundary is exercised as often as its interior.
fn interior_point(rng: &mut Rng, lo: Q, hi: Q) -> Q {
    match rng.below(4) {
        0 => lo,
        1 => hi,
        _ => Q::clamp(rng.q(), lo, hi),
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
        let mut expect = Q::one();
        for _ in 0..e {
            expect = Q::mul(expect, a);
        }
        assert_eq!(a.pow_u32(e), expect);
    }
    assert_eq!(Q::new(2, 3).unwrap().pow_u32(0), Q::one());
    assert_eq!(Q::new(2, 3).unwrap().pow_u32(3), Q::new(8, 27).unwrap());
}

// ---------------------------------------------------------------------------
// Directed modes really are directed
// ---------------------------------------------------------------------------

#[test]
fn down_never_exceeds_up() {
    let mut rng = Rng::new(0xD1AC);
    for _ in 0..30_000 {
        let (a, b) = (rng.q(), rng.q());
        for (lo, hi, mid) in [
            (
                Q::add_dir(a, b, Dir::Down),
                Q::add_dir(a, b, Dir::Up),
                Q::add_dir(a, b, Dir::Nearest),
            ),
            (
                Q::mul_dir(a, b, Dir::Down),
                Q::mul_dir(a, b, Dir::Up),
                Q::mul_dir(a, b, Dir::Nearest),
            ),
        ] {
            assert!(Q::le(lo, hi), "Down > Up for {a}, {b}");
            assert!(
                Q::le(lo, mid) && Q::le(mid, hi),
                "Nearest outside [Down, Up]"
            );
        }
    }
}
