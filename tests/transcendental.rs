//! Root and transcendental functions: accuracy against an exact oracle, and
//! totality over every state.
//!
//! These functions have no exact rational answer, so the checks are of two
//! kinds. **Accuracy** is measured by inverting the function exactly — `sqrt`'s
//! result is squared and compared to the input, `exp`'s is checked against a
//! series computed at far higher precision — so the oracle never needs to
//! compute an irrational value it cannot represent. **Totality** is checked by
//! sweeping every state and every awkward input and asserting only that a value
//! comes back well-formed and classified, never a panic.

mod common;

use common::{rat, zero as oracle_zero, Rng};
use malachite_q::Rational;
use the_q::{Rat, MAX_MAG, Q};

fn one() -> Rational {
    Rational::from_signeds(1i128, 1i128)
}

fn mag(r: &Rational) -> Rational {
    if *r < oracle_zero() {
        -r.clone()
    } else {
        r.clone()
    }
}

/// Relative error of `got` against `want`, as an exact rational.
fn rel_err(got: &Rational, want: &Rational) -> Rational {
    let d = mag(&(got.clone() - want.clone()));
    let scale = {
        let m = mag(want);
        if m > one() {
            m
        } else {
            one()
        }
    };
    d / scale
}

/// `2^-k` as an exact rational, for stating tolerances.
fn eps(k: u32) -> Rational {
    Rational::from_signeds(1i128, 1i128 << k)
}

const SPECIALS: [Q; 5] = [Q::PosSat, Q::NegSat, Q::PosInf, Q::NegInf, Q::Nan];

fn states() -> Vec<Q> {
    let mut v = vec![
        Q::Number(Rat::new(0, 1).unwrap()),
        Q::Number(Rat::new(1, 1).unwrap()),
        Q::Number(Rat::new(-1, 1).unwrap()),
        Q::Number(Rat::new(1, 2).unwrap()),
        Q::Number(Rat::new(-1, 2).unwrap()),
        Q::Number(Rat::new(4, 1).unwrap()),
        Q::Number(Rat::new(MAX_MAG, 1).unwrap()),
        Q::Number(Rat::new(-MAX_MAG, 1).unwrap()),
        Q::Number(Rat::new(1, MAX_MAG).unwrap()),
    ];
    v.extend_from_slice(&SPECIALS);
    v
}

/// Every result must be well-formed and in exactly one class. This is the
/// no-panic, no-malformed-value guarantee, checked on the artifact.
fn assert_total(q: Q, what: &str) {
    if let Q::Number(x) = q {
        common::assert_wf(x, what);
    }
    let c = [q.is_number(), q.is_saturated(), q.is_infinite(), q.is_nan()]
        .iter()
        .filter(|b| **b)
        .count();
    assert_eq!(c, 1, "{what} produced an unclassified value: {q}");
}

// ===========================================================================
// sqrt
// ===========================================================================

#[test]
fn sqrt_matches_the_derived_special_table() {
    assert_eq!(Q::PosInf.sqrt(), Q::PosInf);
    assert_eq!(Q::NegInf.sqrt(), Q::Nan, "no real root of -inf");
    assert_eq!(Q::Nan.sqrt(), Q::Nan);
    assert_eq!(Q::NegSat.sqrt(), Q::Nan, "negative");
    // The one that surprises people: sqrt of (MAX_MAG, inf) is (2^31, inf),
    // which reaches far below MAX_MAG, so no saturation state is sound.
    assert_eq!(
        Q::PosSat.sqrt(),
        Q::Nan,
        "sqrt of a saturated value cannot claim to still be saturated"
    );
    assert_eq!(Q::zero().sqrt(), Q::zero(), "exact");
    assert_eq!(Q::neg_one().sqrt(), Q::Nan, "no real root of a negative");
}

#[test]
fn sqrt_is_exact_on_perfect_squares() {
    for k in 1i64..200 {
        let q = Q::Number(Rat::new(k * k, 1).unwrap());
        assert_eq!(
            q.sqrt(),
            Q::Number(Rat::new(k, 1).unwrap()),
            "sqrt({}) must be exactly {k}",
            k * k
        );
    }
    // Perfect squares of rationals too.
    assert_eq!(
        Q::Number(Rat::new(9, 16).unwrap()).sqrt(),
        Q::Number(Rat::new(3, 4).unwrap())
    );
}

#[test]
fn sqrt_squared_recovers_the_input() {
    // The accuracy check that needs no irrational oracle: square the result and
    // compare against the input exactly.
    let mut rng = Rng::new(0x5EED_0001);
    let mut worst = oracle_zero();
    for _ in 0..20_000 {
        let x = rng.q();
        if x.numerator() <= 0 {
            continue;
        }
        let q = Q::Number(x);
        match q.sqrt() {
            Q::Number(r) => {
                let sq = rat(r) * rat(r);
                let e = rel_err(&sq, &rat(x));
                if e > worst {
                    worst = e.clone();
                }
                assert!(
                    e <= eps(40),
                    "sqrt({x}) = {r}; squaring gives {sq}, relative error {e}"
                );
            }
            other => panic!("sqrt of a positive number must be a number, got {other}"),
        }
    }
    println!("sqrt: worst relative error of r^2 vs x = {worst}");
}

#[test]
fn sqrt_is_accurate_in_the_unit_interval() {
    // The crate's actual working domain, where accuracy matters most.
    let mut rng = Rng::new(0x5EED_0002);
    for _ in 0..20_000 {
        let x = rng.q_unit();
        if x.numerator() == 0 {
            continue;
        }
        if let Q::Number(r) = Q::Number(x).sqrt() {
            let sq = rat(r) * rat(r);
            assert!(
                rel_err(&sq, &rat(x)) <= eps(45),
                "sqrt({x}) = {r} is not accurate enough in [0,1]"
            );
            assert!(rat(r) >= oracle_zero(), "sqrt returned a negative root");
        } else {
            panic!("sqrt of a unit value must be a number");
        }
    }
}

#[test]
fn sqrt_is_monotone() {
    let mut rng = Rng::new(0x5EED_0003);
    for _ in 0..5_000 {
        let (a, b) = (rng.q_unit(), rng.q_unit());
        let (lo, hi) = if Rat::le(a, b) { (a, b) } else { (b, a) };
        let (sl, sh) = (Q::Number(lo).sqrt(), Q::Number(hi).sqrt());
        if let (Q::Number(x), Q::Number(y)) = (sl, sh) {
            // Allow the rounding slack: monotone up to the grid.
            let slack = eps(40);
            assert!(
                rat(x) <= rat(y) + slack,
                "sqrt is not monotone: sqrt({lo})={x} > sqrt({hi})={y}"
            );
        }
    }
}

#[test]
fn sqrt_is_total_and_never_panics() {
    for q in states() {
        assert_total(q.sqrt(), "sqrt");
    }
    let mut rng = Rng::new(0x5EED_0004);
    for _ in 0..20_000 {
        let n = rng.next_u64() as i64;
        let d = rng.next_u64() as i64;
        assert_total(Q::new(n, d).sqrt(), "sqrt");
    }
}

#[test]
fn isqrt_is_correct() {
    use the_q::transcendental::isqrt_i64;
    // Exhaustive over a dense low range, then the boundaries.
    for n in 0i64..10_000 {
        let r = isqrt_i64(n);
        assert!(r * r <= n, "isqrt({n}) = {r} is too large");
        assert!((r + 1) * (r + 1) > n, "isqrt({n}) = {r} is too small");
    }
    for n in [MAX_MAG, MAX_MAG - 1, 1 << 62, (1i64 << 31) * (1i64 << 31)] {
        if n > MAX_MAG {
            continue;
        }
        let r = isqrt_i64(n);
        assert!(
            (r as i128) * (r as i128) <= n as i128,
            "isqrt({n}) too large"
        );
        assert!(
            ((r + 1) as i128) * ((r + 1) as i128) > n as i128,
            "isqrt({n}) too small"
        );
    }
    let mut rng = Rng::new(0x5EED_0005);
    for _ in 0..50_000 {
        let n = (rng.next_u64() % (MAX_MAG as u64 + 1)) as i64;
        let r = isqrt_i64(n);
        assert!(
            (r as i128) * (r as i128) <= n as i128,
            "isqrt({n}) too large"
        );
        assert!(
            ((r + 1) as i128) * ((r + 1) as i128) > n as i128,
            "isqrt({n}) too small"
        );
    }
}
