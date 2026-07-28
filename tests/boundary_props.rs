//! Property tests (proptest, with shrinking) aimed at the parts of the crate
//! the Verus proofs deliberately do not reach.
//!
//! Everything inside `verus!` is machine-checked, so re-testing it here would
//! buy nothing. What is *not* checked is the trusted boundary enumerated in
//! `TRUSTED.md`: `to_f64`, the `f64::to_bits` bridge behind `from_f64_dir`, and
//! the std trait glue. Those are exactly the places where a wrong assumption
//! would be invisible to the solver, and where shrinking a counterexample to
//! its minimal form is worth the dependency.
//!
//! The rounding contract is included as well, at the *achieved* `B = 61` rather
//! than the specification's `B >= 60` bar, so that losing the extra bit shows up
//! as a test failure rather than as silently weaker output.

mod common;

use common::*;
use proptest::prelude::*;
use the_q::convert::{from_f64_dir, to_f64};
use the_q::{Dir, Q};

const DIRS: [Dir; 3] = [Dir::Down, Dir::Up, Dir::Nearest];

/// Arbitrary in-budget `Q`, biased towards the shapes that exercise rounding:
/// large coprime-ish numerator/denominator pairs rather than small integers.
fn arb_q() -> impl Strategy<Value = Q> {
    (any::<i64>(), any::<i64>()).prop_filter_map("constructible", |(n, d)| Q::new(n, d))
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(2000))]

    /// `to_f64` is `external_body`: the proofs say nothing about it. Pin it
    /// against the oracle's exact rational instead.
    #[test]
    fn prop_to_f64_close(q in arb_q()) {
        let f = to_f64(q);
        prop_assert!(f.is_finite(), "to_f64 produced {f} for {q}");
        let exact = rat(q);
        let back = malachite_q::Rational::try_from(f).unwrap();
        let err = rabs(back - exact.clone());
        // A few ulp of headroom: two int->float roundings plus one division.
        let bound = rabs(exact) / rat_of(1i128 << 50, 1) + rat_of(1, 1i128 << 50);
        prop_assert!(err <= bound, "to_f64 too far for {q} -> {f}");
    }

    /// `from_f64_dir` over arbitrary bit patterns. The IEEE decode and the
    /// rounding are verified; the `to_bits` bridge is not, so drive it with
    /// every shape of float including subnormals, infinities and NaN.
    #[test]
    fn prop_from_f64_dir_contract(bits in any::<u64>(), ix in 0usize..3) {
        let v = f64::from_bits(bits);
        let dir = DIRS[ix];
        match from_f64_dir(v, dir) {
            None => {
                // Rejection is only allowed for non-finite or out-of-range input.
                prop_assert!(!v.is_finite() || v.abs() > (1u64 << 61) as f64,
                    "rejected representable {v}");
            }
            Some(q) => {
                assert_wf(q, "from_f64_dir");
                prop_assert!(v.is_finite(), "accepted non-finite {v}");
                let exact = malachite_q::Rational::try_from(v).unwrap();
                assert_r3(q, &exact, "from_f64_dir");
                match dir {
                    Dir::Down => prop_assert!(rat(q) <= exact),
                    Dir::Up => prop_assert!(rat(q) >= exact),
                    Dir::Nearest => {}
                }
            }
        }
    }

    /// The derived `Eq`/`Hash` and the hand-written `Ord` are unverified glue.
    /// Canonical form is what makes them sound, so check them against the
    /// oracle's ordering rather than against each other.
    #[test]
    fn prop_ord_glue_matches_oracle(a in arb_q(), b in arb_q()) {
        let (ra, rb) = (rat(a), rat(b));
        prop_assert_eq!(a.cmp(&b), ra.cmp(&rb), "Ord disagrees with oracle");
        prop_assert_eq!(a == b, ra == rb, "Eq disagrees with oracle");
        if a == b {
            // Canonicality: equal values must be structurally identical, which
            // is what makes the derived Hash correct.
            prop_assert_eq!(a.numerator(), b.numerator());
            prop_assert_eq!(a.denominator(), b.denominator());
        }
    }

    /// R3 at the achieved `B = 61` across the arithmetic surface, with
    /// shrinking — the fixed differential sweeps cover more cases, this one
    /// produces a minimal witness when something breaks.
    #[test]
    fn prop_arith_meets_b61(a in arb_q(), b in arb_q()) {
        let ra = rat(a);
        let rb = rat(b);
        for (name, got, exact) in [
            ("add", Q::add(a, b), ra.clone() + rb.clone()),
            ("sub", Q::sub(a, b), ra.clone() - rb.clone()),
            ("mul", Q::mul(a, b), ra.clone() * rb.clone()),
        ] {
            assert_wf(got, name);
            if magnitude_fits(&exact) {
                assert_r3(got, &exact, name);
                assert_exact_if_representable(got, &exact, name);
            }
        }
        if !b.is_zero() {
            let exact = ra / rb;
            let got = Q::div(a, b);
            assert_wf(got, "div");
            if magnitude_fits(&exact) {
                assert_r3(got, &exact, "div");
                assert_exact_if_representable(got, &exact, "div");
            }
        }
    }
}
