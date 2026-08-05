//! Differential tests against `malachite-q` (obligation: §7 of the spec).
//!
//! For every operation, on random inputs and on exhaustive small inputs, we
//! check three things against an independent arbitrary-precision oracle:
//!
//! * **R1** — if the exact result is representable, `the-q` returned it exactly.
//! * **R2** — `Down <= exact <= Up`.
//! * **R3** — every result is within `2^-61 · max(1, |exact|)` of the exact value.
//!
//! plus the type invariant (I1 + I2) on every value produced.

#![allow(clippy::unusual_byte_groupings)]

mod common;

use common::*;
use malachite_q::Rational;
use the_q::{Dir, Rat};

// ---------------------------------------------------------------------------
// Random differential tests
// ---------------------------------------------------------------------------

#[test]
fn add_matches_oracle() {
    let mut rng = Rng::new(0xA11CE);
    for _ in 0..20_000 {
        let (a, b) = (rng.q(), rng.q());
        let exact = rat(a) + rat(b);
        for dir in DIRS {
            let r = Rat::add_dir(a, b, dir);
            assert_wf(r, "add");
            if magnitude_fits(&exact) {
                assert_exact_if_representable(r, &exact, "add");
                assert_r3(r, &exact, "add");
            }
        }
        if magnitude_fits(&exact) {
            assert_r2(
                Rat::add_dir(a, b, Dir::Down),
                Rat::add_dir(a, b, Dir::Up),
                &exact,
                "add",
            );
        }
    }
}

#[test]
fn sub_matches_oracle() {
    let mut rng = Rng::new(0xB0B);
    for _ in 0..20_000 {
        let (a, b) = (rng.q(), rng.q());
        let exact = rat(a) - rat(b);
        for dir in DIRS {
            let r = Rat::sub_dir(a, b, dir);
            assert_wf(r, "sub");
            if magnitude_fits(&exact) {
                assert_exact_if_representable(r, &exact, "sub");
                assert_r3(r, &exact, "sub");
            }
        }
        if magnitude_fits(&exact) {
            assert_r2(
                Rat::sub_dir(a, b, Dir::Down),
                Rat::sub_dir(a, b, Dir::Up),
                &exact,
                "sub",
            );
        }
    }
}

#[test]
fn mul_matches_oracle() {
    let mut rng = Rng::new(0xC0FFEE);
    for _ in 0..20_000 {
        let (a, b) = (rng.q(), rng.q());
        let exact = rat(a) * rat(b);
        for dir in DIRS {
            let r = Rat::mul_dir(a, b, dir);
            assert_wf(r, "mul");
            if magnitude_fits(&exact) {
                assert_exact_if_representable(r, &exact, "mul");
                assert_r3(r, &exact, "mul");
            }
        }
        if magnitude_fits(&exact) {
            assert_r2(
                Rat::mul_dir(a, b, Dir::Down),
                Rat::mul_dir(a, b, Dir::Up),
                &exact,
                "mul",
            );
        }
    }
}

#[test]
fn div_matches_oracle() {
    let mut rng = Rng::new(0xD15EA5E);
    for _ in 0..20_000 {
        let (a, b) = (rng.q(), rng.q_nonzero());
        let exact = rat(a) / rat(b);
        for dir in DIRS {
            let r = Rat::div_dir(a, b, dir);
            assert_wf(r, "div");
            if magnitude_fits(&exact) {
                assert_exact_if_representable(r, &exact, "div");
                assert_r3(r, &exact, "div");
            }
        }
        if magnitude_fits(&exact) {
            assert_r2(
                Rat::div_dir(a, b, Dir::Down),
                Rat::div_dir(a, b, Dir::Up),
                &exact,
                "div",
            );
        }
    }
}

#[test]
fn unit_interval_ops_are_always_exact_or_bounded() {
    // The engine's real domain: opinions in [0, 1] with moderate denominators.
    let mut rng = Rng::new(0x0B1E_0F17);
    for _ in 0..20_000 {
        let (a, b) = (rng.q_unit(), rng.q_unit());
        for (name, exact, got) in [
            ("add", rat(a) + rat(b), Rat::add(a, b)),
            ("mul", rat(a) * rat(b), Rat::mul(a, b)),
            ("sub", rat(a) - rat(b), Rat::sub(a, b)),
        ] {
            assert_wf(got, name);
            assert_exact_if_representable(got, &exact, name);
            assert_r3(got, &exact, name);
        }
    }
}

// ---------------------------------------------------------------------------
// Exhaustive small inputs
// ---------------------------------------------------------------------------

#[test]
fn exhaustive_small_rationals() {
    // Every p/q with |p| <= 12, 1 <= q <= 12: 300 values, 90_000 pairs, four
    // operations, three directions. Small enough to be exhaustive, wide enough
    // to hit every sign and reduction pattern.
    let mut vals: Vec<Rat> = Vec::new();
    for p in -12i64..=12 {
        for q in 1i64..=12 {
            vals.push(Rat::new(p, q).unwrap());
        }
    }
    for &a in &vals {
        for &b in &vals {
            for dir in DIRS {
                let sum = Rat::add_dir(a, b, dir);
                assert_wf(sum, "add");
                assert_eq!(rat(sum), rat(a) + rat(b), "small add {a} + {b}");

                let dif = Rat::sub_dir(a, b, dir);
                assert_wf(dif, "sub");
                assert_eq!(rat(dif), rat(a) - rat(b), "small sub {a} - {b}");

                let pro = Rat::mul_dir(a, b, dir);
                assert_wf(pro, "mul");
                assert_eq!(rat(pro), rat(a) * rat(b), "small mul {a} * {b}");

                if !b.is_zero() {
                    let quo = Rat::div_dir(a, b, dir);
                    assert_wf(quo, "div");
                    assert_eq!(rat(quo), rat(a) / rat(b), "small div {a} / {b}");
                }
            }
            // Comparison must agree with the oracle's total order.
            let expect = rat(a).cmp(&rat(b));
            let got = a.cmp(&b);
            assert_eq!(got, expect, "cmp {a} vs {b}");
            assert_eq!(Rat::compare(a, b) < 0, expect.is_lt());
            assert_eq!(Rat::compare(a, b) == 0, expect.is_eq());
            assert_eq!(Rat::compare(a, b) > 0, expect.is_gt());
        }
        // Unary operations are exact, always.
        assert_eq!(rat(a.neg()), -rat(a));
        assert_eq!(rat(a.abs()), rabs(rat(a)));
        if !a.is_zero() {
            assert_eq!(rat(a.recip()), one() / rat(a));
            assert_eq!(a.recip().recip(), a, "recip is an involution");
        }
        assert_eq!(a.neg().neg(), a, "neg is an involution");
    }
}

// ---------------------------------------------------------------------------
// The f64 boundary — the differential tests backing TRUSTED.md
// ---------------------------------------------------------------------------

#[test]
fn from_f64_matches_oracle() {
    let mut rng = Rng::new(0xF10A7);
    let mut specials: Vec<f64> = vec![
        0.0,
        -0.0,
        1.0,
        -1.0,
        0.5,
        0.1,
        0.85,
        -0.85,
        1e-30,
        -1e-30,
        f64::MIN_POSITIVE,
        -f64::MIN_POSITIVE,
        5e-324,          // smallest subnormal
        2.0f64.powi(61), // right at the documented magnitude limit
        2.0f64.powi(-61),
        2.0f64.powi(-62),
        2.0f64.powi(-70),
    ];
    for _ in 0..5_000 {
        // Random finite doubles in a sane range.
        let v = (rng.next_u64() as i64 as f64) / (1u64 << 40) as f64;
        if v.is_finite() {
            specials.push(v);
        }
    }
    for v in specials {
        if v.abs() > 2.0f64.powi(61) {
            continue;
        }
        let exact = Rational::try_from(v).expect("finite double is rational");
        for dir in DIRS {
            let got = the_q::convert::from_f64_dir(v, dir).unwrap_or_else(|| {
                panic!("from_f64_dir returned None for finite {v} within range")
            });
            assert_wf(got, "from_f64_dir");
            assert_r3(got, &exact, "from_f64_dir");
            match dir {
                Dir::Down => assert!(rat(got) <= exact, "Down {v}: {} > {exact}", rat(got)),
                Dir::Up => assert!(rat(got) >= exact, "Up {v}: {} < {exact}", rat(got)),
                Dir::Nearest => {}
            }
        }
    }
    // NaN and the infinities are rejected.
    for v in [f64::NAN, f64::INFINITY, f64::NEG_INFINITY] {
        for dir in DIRS {
            assert!(the_q::convert::from_f64_dir(v, dir).is_none());
        }
    }
}

#[test]
fn to_f64_is_within_four_ulp() {
    // `to_f64` is the crate's one output-side trusted function. It is not
    // verified; it is pinned here instead.
    let mut rng = Rng::new(0x70F64);
    for _ in 0..20_000 {
        let q = rng.q();
        let got = the_q::convert::to_f64(q);
        let exact = rat(q);
        let back = Rational::try_from(got).unwrap();
        let err = rabs(back - exact.clone());
        // 4 ulp relative: err * 2^50 <= max(1, |exact|)
        let bound = if rabs(exact.clone()) > one() {
            rabs(exact.clone())
        } else {
            one()
        };
        assert!(
            err * Rational::from_signeds(1i128 << 50, 1i128) <= bound,
            "to_f64({q}) = {got} is further than 4 ulp from {exact}"
        );
    }
}

// ---------------------------------------------------------------------------
// Long chains — the accumulation claim, measured
// ---------------------------------------------------------------------------

#[test]
fn long_fold_chain_tracks_oracle() {
    // 10^4 sequential operations, exactly the shape the consuming engine's
    // worst case has. The spec predicts ~k · 2^-61 accumulated relative error.
    let mut rng = Rng::new(0x10CDF01D);
    let mut acc = Rat::from_decimal(5, 1).unwrap();
    let mut oracle = rat(acc);
    let k = 10_000u32;
    for i in 0..k {
        let x = rng.q_unit();
        if i % 3 == 0 {
            acc = Rat::mul(acc, x);
            oracle *= rat(x);
        } else {
            acc = Rat::add(acc, x);
            oracle += rat(x);
            // Keep it in the unit interval so the comparison stays meaningful.
            if oracle > one() {
                acc = Rat::sub(acc, Rat::one());
                oracle -= one();
            }
        }
        assert_wf(acc, "fold");
    }
    let err = rabs(rat(acc) - oracle.clone());
    let bound_num = Rational::from_signeds(k as i128, 1i128);
    let scale = if rabs(oracle.clone()) > one() {
        rabs(oracle.clone())
    } else {
        one()
    };
    assert!(
        err.clone() * two_pow_b() <= bound_num * scale,
        "accumulated error {err} exceeds the k · 2^-61 bound after {k} ops"
    );
}
