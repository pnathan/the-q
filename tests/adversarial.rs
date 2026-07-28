//! Adversarial fixtures: the edges where a bounded rational is most likely to
//! be wrong.
//!
//! Budget-edge denominators, sign edges, `i64::MIN`, magnitude saturation,
//! subnormal doubles, and the documented counterexamples. Each of these is a
//! place where a plausible implementation quietly does the wrong thing.

#![allow(clippy::unusual_byte_groupings)]

mod common;

use common::*;
use the_q::{Dir, MAX_DEC_PLACES, MAX_MAG, Q};

// ---------------------------------------------------------------------------
// The budget edge
// ---------------------------------------------------------------------------

#[test]
fn values_at_the_budget_edge_are_constructible_and_sound() {
    // MAX_MAG is 2^62 - 1, which is odd, so MAX_MAG/MAX_MAG reduces to 1/1 and
    // MAX_MAG/(MAX_MAG - 1) is already in lowest terms.
    let edge = Q::new(MAX_MAG, MAX_MAG).unwrap();
    assert_eq!(edge, Q::one());

    for &n in &[
        MAX_MAG,
        MAX_MAG - 1,
        MAX_MAG - 2,
        1,
        0,
        -1,
        -MAX_MAG + 1,
        -MAX_MAG,
    ] {
        for &d in &[MAX_MAG, MAX_MAG - 1, MAX_MAG - 2, 1, 2] {
            let q = Q::new(n, d).unwrap();
            assert_wf(q, "budget-edge construction");
            assert_eq!(rat(q), rat_of(n as i128, d as i128));
        }
    }
}

#[test]
fn arithmetic_at_the_budget_edge_stays_sound() {
    let candidates: Vec<Q> = [
        (MAX_MAG, 1),
        (-MAX_MAG, 1),
        (MAX_MAG, MAX_MAG - 1),
        (1, MAX_MAG),
        (-1, MAX_MAG),
        (MAX_MAG - 1, MAX_MAG),
        (1, 2),
        (-1, 2),
        (0, 1),
        (1, 1),
        (-1, 1),
    ]
    .iter()
    .map(|&(n, d)| Q::new(n, d).unwrap())
    .collect();

    for &a in &candidates {
        for &b in &candidates {
            for dir in DIRS {
                for (name, exact, got) in [
                    ("add", rat(a) + rat(b), Q::add_dir(a, b, dir)),
                    ("sub", rat(a) - rat(b), Q::sub_dir(a, b, dir)),
                    ("mul", rat(a) * rat(b), Q::mul_dir(a, b, dir)),
                ] {
                    assert_wf(got, name);
                    if magnitude_fits(&exact) {
                        assert_r3(got, &exact, name);
                        assert_exact_if_representable(got, &exact, name);
                    }
                }
                if !b.is_zero() {
                    let exact = rat(a) / rat(b);
                    let got = Q::div_dir(a, b, dir);
                    assert_wf(got, "div");
                    if magnitude_fits(&exact) {
                        assert_r3(got, &exact, "div");
                        assert_exact_if_representable(got, &exact, "div");
                    }
                }
            }
        }
    }
}

#[test]
fn the_finest_grid_step_is_representable() {
    // The dyadic snap's finest grid is 2^-61; that value must itself be a legal
    // Q, otherwise the rounding target does not exist.
    let eps = Q::new(1, 1i64 << 61).unwrap();
    assert_wf(eps, "2^-61");
    assert_eq!(eps.denominator(), 1i64 << 61);
    assert!(eps.denominator() <= MAX_MAG);
    // And 2^62 is *not* representable — that is the budget doing its job.
    assert!(Q::new(1, 1i64 << 62).is_none());
    assert!(Q::new(1i64 << 62, 1).is_none());
}

// ---------------------------------------------------------------------------
// Sign edges and i64::MIN
// ---------------------------------------------------------------------------

#[test]
fn i64_min_is_rejected_everywhere() {
    // |i64::MIN| is not an i64 at all, and it is outside I2 regardless. Every
    // entry point must reject it rather than wrap.
    assert!(Q::from_int(i64::MIN).is_none());
    assert!(Q::new(i64::MIN, 1).is_none());
    assert!(Q::new(1, i64::MIN).is_none());
    assert!(Q::new(i64::MIN, i64::MIN).is_none() || Q::new(i64::MIN, i64::MIN) == Some(Q::one()));
    assert!(Q::from_decimal(i64::MIN, 0).is_none());
    // The rounding constructor is total for a non-zero denominator, and still
    // returns something well-formed.
    for dir in DIRS {
        let q = Q::new_rounded(i64::MIN, 1, dir).unwrap();
        assert_wf(q, "new_rounded(i64::MIN, 1)");
        let q = Q::new_rounded(1, i64::MIN, dir).unwrap();
        assert_wf(q, "new_rounded(1, i64::MIN)");
        assert!(Q::new_rounded(1, 0, dir).is_none());
    }
    // i64::MAX is above MAX_MAG too.
    assert!(Q::from_int(i64::MAX).is_none());
    assert!(Q::from_int(MAX_MAG).is_some());
    assert!(Q::from_int(-MAX_MAG).is_some());
    assert!(Q::from_int(MAX_MAG + 1).is_none());
}

#[test]
fn negative_denominators_are_normalised() {
    for &(n, d) in &[(1i64, -2i64), (-1, -2), (-1, 2), (0, -7), (-6, -8), (6, -8)] {
        let q = Q::new(n, d).unwrap();
        assert!(
            q.denominator() > 0,
            "denominator not normalised for {n}/{d}"
        );
        assert_wf(q, "sign normalisation");
        assert_eq!(rat(q), rat_of(n as i128, d as i128));
    }
    // Zero has exactly one representation.
    for d in [-9i64, -1, 1, 9, MAX_MAG, -MAX_MAG] {
        assert_eq!(Q::new(0, d).unwrap(), Q::zero());
        assert_eq!(Q::new(0, d).unwrap().denominator(), 1);
    }
}

#[test]
fn signum_and_predicates_at_the_edges() {
    assert_eq!(Q::zero().signum(), 0);
    assert_eq!(Q::one().signum(), 1);
    assert_eq!(Q::one().neg().signum(), -1);
    assert_eq!(Q::new(-1, MAX_MAG).unwrap().signum(), -1);
    assert!(Q::zero().in_unit_interval());
    assert!(Q::one().in_unit_interval());
    assert!(Q::new(1, MAX_MAG).unwrap().in_unit_interval());
    assert!(!Q::new(-1, MAX_MAG).unwrap().in_unit_interval());
    assert!(!Q::new(MAX_MAG, MAX_MAG - 1).unwrap().in_unit_interval());
    assert!(Q::one().is_one());
    assert!(Q::new(2, 2).unwrap().is_one()); // 2/2 canonicalises to 1/1
    assert!(Q::zero().is_zero());
}

// ---------------------------------------------------------------------------
// Magnitude saturation — the one case R3 cannot cover
// ---------------------------------------------------------------------------

#[test]
fn magnitude_overflow_saturates_and_checked_reports_it() {
    let big = Q::from_int(MAX_MAG).unwrap();

    // MAX_MAG + MAX_MAG is not representable: no Q has that magnitude.
    let exact = rat(big) + rat(big);
    assert!(!magnitude_fits(&exact));
    assert!(Q::checked_add(big, big).is_none());
    let sat = Q::add(big, big);
    assert_wf(sat, "saturated add");
    assert_eq!(sat, big, "saturation should clamp to +MAX_MAG");

    // And on the negative side.
    let nbig = big.neg();
    assert!(Q::checked_add(nbig, nbig).is_none());
    assert_eq!(Q::add(nbig, nbig), nbig);

    // MAX_MAG * MAX_MAG likewise.
    assert!(Q::checked_mul(big, big).is_none());
    assert_eq!(Q::mul(big, big), big);
    assert!(Q::checked_sub(nbig, big).is_none());

    // Anything that *does* fit is reported as Some and agrees with the plain op.
    let half = Q::new(1, 2).unwrap();
    assert_eq!(Q::checked_add(half, half), Some(Q::one()));
    assert_eq!(Q::checked_mul(half, half), Some(Q::new(1, 4).unwrap()));
    assert_eq!(Q::checked_sub(half, half), Some(Q::zero()));

    // Division by a tiny value is the other way to leave the budget.
    let tiny = Q::new(1, MAX_MAG).unwrap();
    let q = Q::div(Q::one(), tiny);
    assert_wf(q, "div by 1/MAX_MAG");
    assert_eq!(q, big);
    let q = Q::div(big, tiny);
    assert_wf(q, "saturating div");
    assert_eq!(q, big, "should saturate, not wrap");
}

#[test]
fn saturation_never_produces_an_invalid_value() {
    // Hammer the saturation path from every direction and sign.
    let mut rng = Rng::new(0x5A7);
    let bigs: Vec<Q> = [
        (MAX_MAG, 1),
        (-MAX_MAG, 1),
        (MAX_MAG, 2),
        (-MAX_MAG, 3),
        (MAX_MAG - 1, 1),
    ]
    .iter()
    .map(|&(n, d)| Q::new(n, d).unwrap())
    .collect();
    for _ in 0..5_000 {
        let a = bigs[rng.below(bigs.len() as u64) as usize];
        let b = bigs[rng.below(bigs.len() as u64) as usize];
        for dir in DIRS {
            assert_wf(Q::add_dir(a, b, dir), "sat add");
            assert_wf(Q::sub_dir(a, b, dir), "sat sub");
            assert_wf(Q::mul_dir(a, b, dir), "sat mul");
            if !b.is_zero() {
                assert_wf(Q::div_dir(a, b, dir), "sat div");
            }
        }
    }
}

// ---------------------------------------------------------------------------
// from_decimal edges
// ---------------------------------------------------------------------------

#[test]
fn from_decimal_edges() {
    assert_eq!(Q::from_decimal(1, 0).unwrap(), Q::one());
    assert!(Q::from_decimal(1, MAX_DEC_PLACES).is_some());
    assert!(Q::from_decimal(1, MAX_DEC_PLACES + 1).is_none());
    assert!(Q::from_decimal(1, 255).is_none());
    assert!(Q::from_decimal(MAX_MAG, 0).is_some());
    assert!(Q::from_decimal(MAX_MAG + 1, 0).is_none());
    // 10^18 is representable; the resulting value is 1/10^18 exactly.
    let tiny = Q::from_decimal(1, 18).unwrap();
    assert_eq!(tiny.denominator(), 1_000_000_000_000_000_000);
    assert_eq!(tiny.numerator(), 1);
    // Reduction happens: 0.50 is 1/2, not 50/100.
    assert_eq!(Q::from_decimal(50, 2).unwrap(), Q::new(1, 2).unwrap());
    // Every 4-place decimal is exact.
    for m in -20000i64..=20000 {
        let q = Q::from_decimal(m, 4).unwrap();
        assert_eq!(rat(q), rat_of(m as i128, 10_000i128));
    }
}

// ---------------------------------------------------------------------------
// f64 edges
// ---------------------------------------------------------------------------

#[test]
fn f64_boundary_edges() {
    use the_q::convert::from_f64_dir;
    // Zero, both signs.
    assert_eq!(from_f64_dir(0.0, Dir::Nearest).unwrap(), Q::zero());
    assert_eq!(from_f64_dir(-0.0, Dir::Nearest).unwrap(), Q::zero());
    // Exact powers of two round-trip exactly.
    for e in -60i32..=61 {
        let v = 2.0f64.powi(e);
        for dir in DIRS {
            let q = from_f64_dir(v, dir).unwrap();
            assert_wf(q, "power of two");
            assert_eq!(
                rat(q),
                malachite_q::Rational::try_from(v).unwrap(),
                "2^{e} did not convert exactly under {dir:?}"
            );
        }
    }
    // Values below the finest grid: Nearest gives zero, the directed modes stay
    // on their side of the value.
    for v in [5e-324f64, 1e-300, 2.0f64.powi(-100)] {
        assert_eq!(from_f64_dir(v, Dir::Nearest).unwrap(), Q::zero());
        assert!(
            rat(from_f64_dir(v, Dir::Down).unwrap()) <= malachite_q::Rational::try_from(v).unwrap()
        );
        assert!(
            rat(from_f64_dir(v, Dir::Up).unwrap()) >= malachite_q::Rational::try_from(v).unwrap()
        );
        assert_eq!(from_f64_dir(-v, Dir::Nearest).unwrap(), Q::zero());
        assert!(
            rat(from_f64_dir(-v, Dir::Down).unwrap())
                <= malachite_q::Rational::try_from(-v).unwrap()
        );
        assert!(
            rat(from_f64_dir(-v, Dir::Up).unwrap()) >= malachite_q::Rational::try_from(-v).unwrap()
        );
    }
    // Out of range in magnitude.
    assert!(from_f64_dir(2.0f64.powi(62), Dir::Nearest).is_none());
    assert!(from_f64_dir(f64::MAX, Dir::Nearest).is_none());
    assert!(from_f64_dir(-f64::MAX, Dir::Nearest).is_none());
    // Non-finite.
    assert!(from_f64_dir(f64::NAN, Dir::Nearest).is_none());
    assert!(from_f64_dir(f64::INFINITY, Dir::Nearest).is_none());
    assert!(from_f64_dir(f64::NEG_INFINITY, Dir::Nearest).is_none());
    // 0.1 is not a decimal in binary; the conversion is of the *double*, not of
    // the literal a human typed.
    let q = from_f64_dir(0.1, Dir::Nearest).unwrap();
    assert_ne!(q, Q::from_decimal(1, 1).unwrap());
    // ...which is exactly why from_decimal exists.
    assert_eq!(Q::from_decimal(1, 1).unwrap(), Q::new(1, 10).unwrap());
}

// ---------------------------------------------------------------------------
// The documented counterexamples
// ---------------------------------------------------------------------------

#[test]
fn associativity_can_fail_when_rounding_bites() {
    // The README claims add is not associative in general. If this test ever
    // starts failing, the claim has become too pessimistic and the docs should
    // be revisited — it is here to keep the documentation honest, in both
    // directions.
    let mut rng = Rng::new(0xA55_0C_1A);
    let mut found = false;
    for _ in 0..200_000 {
        let (a, b, c) = (rng.q(), rng.q(), rng.q());
        if Q::add(Q::add(a, b), c) != Q::add(a, Q::add(b, c)) {
            found = true;
            break;
        }
    }
    assert!(
        found,
        "no associativity failure found — the README's honesty note may be stale"
    );
}

#[test]
fn the_composed_operation_is_not_globally_monotone() {
    // README documents this, and R4 is stated per-grid because of it: "return
    // it exactly if it fits, otherwise snap to the dyadic grid" is not monotone
    // across the fits/does-not-fit boundary.
    //
    // `u` is representable and sits strictly inside the grid cell
    // `(2^-61, 2·2^-61)`, so it is returned untouched. `v` is a hair larger but
    // *not* representable, so it snaps down to the bottom of that same cell —
    // which is below `u`. Rounding down has inverted the order.
    let g: i64 = 1i64 << 61;
    let u = Q::new(2, g + 1).unwrap();
    let scale = Q::new(MAX_MAG, MAX_MAG - 1).unwrap(); // 1 + 1/(MAX_MAG-1)
    let v_exact = rat(u) * rat(scale);
    let v = Q::mul_dir(u, scale, Dir::Down);
    assert!(rat(u) < v_exact, "setup: u must be strictly below v");
    assert!(
        Q::lt(v, u),
        "expected round_down to invert the order; the monotonicity note may be stale"
    );
    assert_eq!(
        v,
        Q::new(1, g).unwrap(),
        "v should snap to the cell floor 2^-61"
    );
}

#[test]
fn rounding_is_monotone_within_one_grid() {
    // R4 as actually claimed: on a fixed grid, snapping preserves order. Every
    // value in (0, 1) uses the same grid (step 2^-61), so this exercises the
    // per-grid statement directly, on exact results that all genuinely round.
    let mut rng = Rng::new(0xB0_0_1);
    // Wide unit-interval values: denominators near the budget, so products land
    // at ~2^124 and essentially always need rounding.
    let wide = |r: &mut Rng| loop {
        let d = MAX_MAG - r.below(1024) as i64;
        let n = r.below(d as u64) as i64;
        if let Some(q) = Q::new(n, d) {
            return q;
        }
    };
    let mut checked = 0u32;
    for _ in 0..40_000 {
        let (a, b) = (wide(&mut rng), wide(&mut rng));
        let (c, d) = (wide(&mut rng), wide(&mut rng));
        let (x_exact, y_exact) = (rat(a) * rat(b), rat(c) * rat(d));
        // Only the rounding path is interesting here.
        if fits_budget(&x_exact) || fits_budget(&y_exact) {
            continue;
        }
        let (lo_pair, hi_pair) = if x_exact <= y_exact {
            ((a, b), (c, d))
        } else {
            ((c, d), (a, b))
        };
        for dir in DIRS {
            let lo = Q::mul_dir(lo_pair.0, lo_pair.1, dir);
            let hi = Q::mul_dir(hi_pair.0, hi_pair.1, dir);
            assert!(
                Q::le(lo, hi),
                "grid rounding inverted order under {dir:?}: {lo} > {hi}"
            );
        }
        checked += 1;
    }
    assert!(
        checked > 1_000,
        "not enough rounding-path samples ({checked})"
    );
}

// ---------------------------------------------------------------------------
// Long chains at the edge
// ---------------------------------------------------------------------------

#[test]
fn ten_thousand_op_chain_at_the_budget_edge() {
    // Denominators deliberately pushed against the budget on every step, so
    // essentially every operation takes the rounding path.
    let mut rng = Rng::new(0xE_D_9_E);
    let mut acc = Q::new(MAX_MAG - 1, MAX_MAG).unwrap();
    let mut oracle = rat(acc);
    for i in 0..10_000u32 {
        let x = Q::new(
            (rng.next_u64() % (MAX_MAG as u64)) as i64,
            (rng.next_u64() % (MAX_MAG as u64)) as i64 + 1,
        )
        .unwrap();
        if i % 2 == 0 {
            acc = Q::mul(acc, x);
            oracle *= rat(x);
        } else {
            acc = Q::sub(Q::max(acc, x), Q::min(acc, x));
            oracle = rabs(oracle - rat(x));
        }
        assert_wf(acc, "edge chain");
        assert!(acc.denominator() <= MAX_MAG);
        assert!(acc.numerator().unsigned_abs() <= MAX_MAG as u64);
    }
}

#[test]
fn deep_reciprocal_chain_is_exact() {
    // recip is claimed exact in both directions; a long alternating chain must
    // therefore return to where it started, bit for bit.
    let mut rng = Rng::new(0x12_EC_19);
    for _ in 0..5_000 {
        let a = rng.q_nonzero();
        let mut x = a;
        for _ in 0..100 {
            x = x.recip();
        }
        assert_eq!(x, a, "even-length recip chain drifted from {a}");
    }
}
