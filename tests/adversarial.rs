//! Adversarial fixtures: the edges where a bounded rational is most likely to
//! be wrong.
//!
//! Budget-edge denominators, sign edges, `i64::MIN`, magnitude saturation,
//! subnormal doubles, and the documented counterexamples. Each of these is a
//! place where a plausible implementation quietly does the wrong thing.

#![allow(clippy::unusual_byte_groupings)]

mod common;

use common::*;
use malachite_base::num::arithmetic::traits::Pow;
use malachite_q::Rational;
use the_q::convert::{from_f64_dir, from_parts_dir};
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

    // checked_div reports the same saturating cases as None, and reports
    // in-budget quotients as Some, agreeing with the plain op — the same
    // contract checked_add/checked_sub/checked_mul already carry.
    // `MAX_MAG / (1/MAX_MAG) == MAX_MAG^2`, well past the ceiling.
    assert!(Q::checked_div(big, tiny).is_none());
    // `1 / (1/MAX_MAG) == MAX_MAG` exactly — right at the ceiling, not over
    // it, so this one is `Some`.
    assert_eq!(Q::checked_div(Q::one(), tiny), Some(big));
    assert_eq!(Q::checked_div(half, half), Some(Q::one()));
    assert_eq!(Q::checked_div(big, big), Some(Q::one()));
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
fn associativity_defect_for_add_is_quantitatively_bounded() {
    // The test above shows `add` can fail to be associative. This one shows
    // that failure is not unbounded: it demonstrates
    // `laws::theorem_add_associativity_bound` on a genuine failure instance —
    // `|((a+b)+c) - (a+(b+c))| <= 4 * 2^-61 * m`, where `m` bounds
    // `max(1, |exact value|)` for every one of the four additions the two
    // bracketings perform.
    let mut rng = Rng::new(0xA55_0C_1A);
    let mut checked_a_failure = false;
    for _ in 0..200_000 {
        let (a, b, c) = (rng.q(), rng.q(), rng.q());
        let left = Q::add(Q::add(a, b), c);
        let right = Q::add(a, Q::add(b, c));
        if left == right {
            continue;
        }
        checked_a_failure = true;

        let ab = Q::add(a, b);
        let bc = Q::add(b, c);
        let ab_exact = rat(a) + rat(b);
        let bc_exact = rat(b) + rat(c);
        let left_inner_exact = rat(ab) + rat(c);
        let right_inner_exact = rat(a) + rat(bc);

        let mut m = one();
        for exact in [&ab_exact, &bc_exact, &left_inner_exact, &right_inner_exact] {
            let mag = rabs(exact.clone());
            if mag > m {
                m = mag;
            }
        }

        let err = rabs(rat(left) - rat(right));
        // Division-free, matching the theorem's own statement:
        // |left - right| * 2^61 <= 4 * m.
        assert!(
            err.clone() * two_pow_b()
                <= malachite_q::Rational::from_signeds(4i128, 1i128) * m.clone(),
            "associativity defect exceeded the proven bound: a={a:?} b={b:?} c={c:?}, \
             left={left:?} right={right:?}, err={err}, m={m}"
        );
    }
    assert!(
        checked_a_failure,
        "no associativity failure found to check the bound against"
    );
}

#[test]
fn associativity_defect_for_mul_is_quantitatively_bounded_on_unit_interval() {
    // The multiplicative analogue: `laws::theorem_mul_associativity_bound_unit_interval`
    // claims `|((a*b)*c) - (a*(b*c))| <= 6 * 2^-61` whenever `a, b, c` all lie
    // in `[0, 1]`. Draw wide unit-interval values (denominators near the
    // budget, so rounding is essentially guaranteed) until a genuine
    // associativity failure turns up, and check the bound on it.
    let mut rng = Rng::new(0x0FF_1CE);
    let wide01 = |r: &mut Rng| loop {
        let d = MAX_MAG - r.below(1024) as i64;
        let n = r.below((d as u64) + 1) as i64;
        if let Some(q) = Q::new(n, d) {
            return q;
        }
    };
    let mut checked_a_failure = false;
    for _ in 0..200_000 {
        let (a, b, c) = (wide01(&mut rng), wide01(&mut rng), wide01(&mut rng));
        assert!(a.in_unit_interval() && b.in_unit_interval() && c.in_unit_interval());
        let left = Q::mul(Q::mul(a, b), c);
        let right = Q::mul(a, Q::mul(b, c));
        if left == right {
            continue;
        }
        checked_a_failure = true;

        let err = rabs(rat(left) - rat(right));
        // |left - right| * 2^61 <= 6.
        assert!(
            err.clone() * two_pow_b() <= malachite_q::Rational::from_signeds(6i128, 1i128),
            "multiplicative associativity defect exceeded the proven bound: \
             a={a:?} b={b:?} c={c:?}, left={left:?} right={right:?}, err={err}"
        );
    }
    assert!(
        checked_a_failure,
        "no associativity failure found to check the bound against"
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

/// The rounding carry: a deterministic witness for the one path the `B = 61`
/// shift introduces that `B = 60` did not have.
///
/// With `s = 62 - k` the scaled numerator can reach `2^62 - 1`, and rounding
/// away from zero then lands on `2^62` — one past `MAX_MAG`. `lemma_carry_reduces`
/// proves the GCD reduction rescues it; this pins the behaviour at runtime,
/// because the random sweeps cannot plausibly reach it (the scaled numerator has
/// to fall in the top `rd`-wide window below `2^62` *and* round up, which is
/// about a `rd / 2^62` chance per snap).
///
/// `x = (3·2^61 − 1) / 3` is just under `2^61`, so `k = 61`, `s = 1`, and the
/// scaled numerator is exactly `2^62 − 1`.
#[test]
fn rounding_carry_reduces_back_into_budget() {
    let n = 3 * (1i64 << 61) - 1;

    let up = Q::new_rounded(n, 3, Dir::Up).expect("representable after reduction");
    assert_eq!(
        (up.numerator(), up.denominator()),
        (1i64 << 61, 1),
        "carry did not reduce: got {up}"
    );
    assert_wf(up, "carry (Up)");

    // The mirror image: rounding a negative value away from zero.
    let down = Q::new_rounded(-n, 3, Dir::Down).expect("representable after reduction");
    assert_eq!(
        (down.numerator(), down.denominator()),
        (-(1i64 << 61), 1),
        "negative carry did not reduce: got {down}"
    );
    assert_wf(down, "carry (Down)");

    // Rounding the other way lands on the last grid point below, `2^62 - 1`
    // over `2^1`. That numerator is odd, so nothing reduces and it sits exactly
    // on `MAX_MAG` — in budget, and the boundary the carry steps one past.
    let no_carry = Q::new_rounded(n, 3, Dir::Down).expect("representable");
    assert_eq!(
        (no_carry.numerator(), no_carry.denominator()),
        (MAX_MAG, 2),
        "Down should have stopped at the last grid point: got {no_carry}"
    );
    assert_wf(no_carry, "carry (no-carry direction)");
}

// ---------------------------------------------------------------------------
// Issue #9: the ingestion constructors' newly-stated value behaviour
//
// Each test here targets a postcondition that the proofs now carry and
// previously did not. They are deliberately executable rather than trusting
// the `ensures`: a postcondition can be proved and still describe the wrong
// thing, and these pin the arithmetic a reader would actually expect.
// ---------------------------------------------------------------------------

/// `Q::new`'s completeness direction: in-budget inputs always produce a value.
///
/// The old contract said only what the answer *is* when there is one, which an
/// implementation returning `None` for every nonzero denominator satisfies.
#[test]
fn new_succeeds_for_every_in_budget_pair() {
    let mut rng = Rng::new(0x9e37_79b9);
    for _ in 0..20_000 {
        // Uniform over the whole in-budget range, both signs, including the
        // exact endpoints.
        let num = (rng.next_u64() % (2 * MAX_MAG as u64 + 1)) as i64 - MAX_MAG;
        let den_mag = (rng.next_u64() % (MAX_MAG as u64)) as i64 + 1;
        let den = if rng.next_u64() & 1 == 0 {
            den_mag
        } else {
            -den_mag
        };
        let q = Q::new(num, den)
            .unwrap_or_else(|| panic!("Q::new({num}, {den}) returned None but both fit"));
        assert_wf(q, "Q::new in budget");
    }
    for (num, den) in [
        (MAX_MAG, MAX_MAG),
        (-MAX_MAG, MAX_MAG),
        (MAX_MAG, -MAX_MAG),
        (0, MAX_MAG),
        (1, MAX_MAG),
        (MAX_MAG, 1),
    ] {
        assert!(
            Q::new(num, den).is_some(),
            "Q::new({num}, {den}) is in budget and must succeed"
        );
    }
    // And the boundary is genuinely a boundary, so the clause is not vacuous.
    assert!(
        Q::new(i64::MAX, 1).is_none(),
        "i64::MAX is one past the budget"
    );
}

/// `from_decimal` is exactly `mantissa / 10^dec_places`, and fails only where
/// its two documented guards say it does.
#[test]
fn from_decimal_is_the_exact_decimal_it_claims() {
    let mut rng = Rng::new(0x5bf0_3635);
    for _ in 0..20_000 {
        let dec_places = (rng.next_u64() % 19) as u8;
        let mantissa = (rng.next_u64() % (2 * MAX_MAG as u64 + 1)) as i64 - MAX_MAG;
        let q = Q::from_decimal(mantissa, dec_places)
            .unwrap_or_else(|| panic!("from_decimal({mantissa}, {dec_places}) must succeed"));
        let scale = 10i128.pow(dec_places as u32);
        assert_eq!(
            rat(q),
            rat_of(mantissa as i128, scale),
            "from_decimal({mantissa}, {dec_places}) is not {mantissa}/10^{dec_places}"
        );
        assert_wf(q, "from_decimal");
    }
    // The doc comment's own example, which had no verified meaning before.
    assert_eq!(Q::from_decimal(85, 2).unwrap().to_string(), "17/20");
    // Both failure guards, and nothing else.
    assert!(
        Q::from_decimal(1, 19).is_none(),
        "19 decimal places is out of range"
    );
    assert!(
        Q::from_decimal(i64::MAX, 0).is_none(),
        "mantissa past MAX_MAG"
    );
    assert!(
        Q::from_decimal(MAX_MAG, 18).is_some(),
        "both guards satisfied"
    );
}

/// `new_rounded` rounds the *value* `num/den`, so a negative denominator does
/// not mirror the direction. This is what `signed_den_num` encodes, and it is
/// the part of the contract most likely to have been written backwards.
#[test]
fn new_rounded_direction_is_about_the_value_not_the_numerator() {
    // 1/3 is not representable, so both directions actually round.
    let a_down = Q::new_rounded(1, 3, Dir::Down).unwrap();
    let a_up = Q::new_rounded(1, 3, Dir::Up).unwrap();
    assert_r2(a_down, a_up, &rat_of(1, 3), "1/3");

    // Same value, both signs flipped. Down must still be the lower of the two.
    let b_down = Q::new_rounded(-1, -3, Dir::Down).unwrap();
    let b_up = Q::new_rounded(-1, -3, Dir::Up).unwrap();
    assert_r2(b_down, b_up, &rat_of(1, 3), "-1/-3");
    assert_eq!(
        rat(a_down),
        rat(b_down),
        "1/3 and -1/-3 must round identically"
    );
    assert_eq!(rat(a_up), rat(b_up), "1/3 and -1/-3 must round identically");

    // A genuinely negative value brackets on the other side of zero.
    let c_down = Q::new_rounded(1, -3, Dir::Down).unwrap();
    let c_up = Q::new_rounded(1, -3, Dir::Up).unwrap();
    assert_r2(c_down, c_up, &rat_of(-1, 3), "1/-3");

    // R3 across a random sweep, including the saturating inputs where the
    // contract is scoped out and only well-formedness is claimed.
    let mut rng = Rng::new(0x1d8e_4f21);
    for _ in 0..20_000 {
        let num = rng.next_u64() as i64;
        let den = rng.next_u64() as i64;
        if den == 0 {
            assert!(Q::new_rounded(num, den, Dir::Nearest).is_none());
            continue;
        }
        let exact = rat_of(num as i128, den as i128);
        let r = Q::new_rounded(num, den, Dir::Nearest).unwrap();
        assert_wf(r, "new_rounded");
        if magnitude_fits(&exact) {
            assert_r3(r, &exact, "new_rounded");
        }
    }
}

/// The sub-grid branch of `from_f64_dir`: values below `2^-62` land on the
/// endpoint of the first dyadic cell, on the correct side.
///
/// This is the branch `lemma_round_frac_subgrid` covers — the one whose
/// denominator is past what `round_frac_exec` accepts, so it cannot inherit the
/// rounder's contract and needed its own proof.
#[test]
fn subnormal_inputs_land_on_the_first_grid_cell() {
    let eps = 1i64 << 61;
    for v in [f64::MIN_POSITIVE, 5e-324, 1e-300, 2f64.powi(-100)] {
        for &(neg, sign) in &[(false, 1i64), (true, -1i64)] {
            let x = if neg { -v } else { v };
            let exact = Rational::try_from(x).expect("finite");

            let near = from_f64_dir(x, Dir::Nearest).unwrap();
            assert_eq!(rat(near), zero(), "Nearest must collapse {x} to zero");

            let down = from_f64_dir(x, Dir::Down).unwrap();
            let up = from_f64_dir(x, Dir::Up).unwrap();
            assert_r2(down, up, &exact, "subgrid");

            // The directed mode that has to move lands exactly on ±1/2^61;
            // the other one stays at zero.
            let (moved, stayed) = if neg { (down, up) } else { (up, down) };
            assert_eq!(
                (moved.numerator(), moved.denominator()),
                (sign, eps),
                "{x} should have rounded to {sign}/2^61"
            );
            assert_eq!(rat(stayed), zero(), "the other direction stays at zero");
            assert_wf(moved, "subgrid endpoint");
            assert_wf(stayed, "subgrid zero");
        }
    }
}

/// `from_parts_dir` — the verified core — agrees with the exact rational its
/// arguments denote, for every direction, across the full exponent range.
///
/// `from_f64_dir` can state no contract at all (nothing in Verus relates an
/// `f64` to a rational), so this is where the differential check belongs.
#[test]
fn from_parts_dir_matches_the_rational_its_arguments_denote() {
    let mut rng = Rng::new(0x2f6b_c0de);
    let mut rounded = 0usize;
    for _ in 0..20_000 {
        let mant = rng.next_u64() % 9_007_199_254_740_993;
        let e = (rng.next_u64() % 2046) as i32 - 1074;
        let neg = rng.next_u64() & 1 == 0;

        let m = Rational::from(mant);
        let scale = if e >= 0 {
            Rational::from(2u32).pow(e as i64)
        } else {
            Rational::from(1) / Rational::from(2u32).pow((-e) as i64)
        };
        let exact = if neg { -(m * scale) } else { m * scale };

        for dir in [Dir::Nearest, Dir::Down, Dir::Up] {
            match from_parts_dir(neg, mant, e, dir) {
                Some(q) => {
                    assert_wf(q, "from_parts_dir");
                    assert_r3(q, &exact, "from_parts_dir");
                    if rat(q) != exact {
                        rounded += 1;
                    }
                }
                None => {
                    // `None` only above the documented 2^61 ceiling.
                    assert!(
                        rabs(exact.clone()) > Rational::from(2u32).pow(61i64),
                        "from_parts_dir({neg}, {mant}, {e}) returned None inside the ceiling"
                    );
                }
            }
        }
    }
    assert!(
        rounded > 0,
        "the sweep never rounded, so R3 was never exercised"
    );
}
