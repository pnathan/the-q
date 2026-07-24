//! Differential tests against malachite-q (the exact-arithmetic oracle).
//!
//! Every op: exhaustive small inputs (always exact per R1) plus random
//! inputs where rounded results are checked against the R1/R2/R3 contract.

mod common;

use common::*;
use malachite_base::num::arithmetic::traits::Abs;
use malachite_q::Rational;
use the_q::{Dir, Q};

#[test]
fn exhaustive_small_ops_are_exact() {
    let mut cases = vec![];
    for n in -6i64..=6 {
        for d in 1i64..=6 {
            cases.push(Q::new(n, d).unwrap());
        }
    }
    for &a in &cases {
        for &b in &cases {
            let (ra, rb) = (rat(a), rat(b));
            for dir in DIRS {
                check_rounding_contract(a.add_dir(b, dir), &(&ra + &rb), dir, "add");
                check_rounding_contract(a.sub_dir(b, dir), &(&ra - &rb), dir, "sub");
                check_rounding_contract(a.mul_dir(b, dir), &(&ra * &rb), dir, "mul");
                if !b.is_zero() {
                    check_rounding_contract(a.div_dir(b, dir), &(&ra / &rb), dir, "div");
                }
            }
            // small results always fit: nearest results are exactly the oracle
            assert_eq!(rat(a.add(b)), &ra + &rb);
            assert_eq!(rat(a.sub(b)), &ra - &rb);
            assert_eq!(rat(a.mul(b)), &ra * &rb);
            if !b.is_zero() {
                assert_eq!(rat(a.div(b)), &ra / &rb);
            }
        }
    }
}

#[test]
fn random_ops_meet_contract() {
    let mut rng = Rng::new(0xC0FFEE);
    for i in 0..4000 {
        // mix of magnitudes: small, medium, budget-edge
        let bits = [(20, 20), (40, 40), (62, 62), (62, 20), (20, 62)][i % 5];
        let a = rand_q(&mut rng, bits.0, bits.1);
        let b = rand_q(&mut rng, bits.1, bits.0);
        let (ra, rb) = (rat(a), rat(b));
        let dir = DIRS[i % 3];
        check_rounding_contract(a.add_dir(b, dir), &(&ra + &rb), dir, "add");
        check_rounding_contract(a.sub_dir(b, dir), &(&ra - &rb), dir, "sub");
        check_rounding_contract(a.mul_dir(b, dir), &(&ra * &rb), dir, "mul");
        if !b.is_zero() {
            check_rounding_contract(a.div_dir(b, dir), &(&ra / &rb), dir, "div");
        }
    }
}

#[test]
fn unary_ops_exact() {
    let mut rng = Rng::new(42);
    for _ in 0..2000 {
        let a = rand_q(&mut rng, 62, 62);
        let ra = rat(a);
        assert_eq!(rat(a.neg()), -&ra);
        assert_eq!(rat(a.abs()), (&ra).abs());
        assert_canonical(a.neg());
        assert_canonical(a.abs());
        if !a.is_zero() {
            let r = a.recip();
            assert_canonical(r);
            assert_eq!(rat(r) * &ra, Rational::from(1));
        }
    }
}

#[test]
fn comparisons_agree_with_oracle() {
    let mut rng = Rng::new(7);
    for _ in 0..2000 {
        let a = rand_q(&mut rng, 62, 62);
        let b = rand_q(&mut rng, 62, 62);
        let (ra, rb) = (rat(a), rat(b));
        assert_eq!(a.le(b), ra <= rb);
        assert_eq!(a.lt(b), ra < rb);
        assert_eq!(a.eq_q(b), ra == rb);
        assert_eq!(a.cmp_q(b), ra.cmp(&rb));
        assert_eq!(a == b, ra == rb, "structural == must be mathematical ==");
    }
}

#[test]
fn from_decimal_matches_oracle() {
    let mut rng = Rng::new(0xDEC1);
    for places in 0u8..=18 {
        let den = 10i64.pow(places as u32);
        for _ in 0..200 {
            let m = rng.i64_in(-1_000_000_000, 1_000_000_000);
            let q = Q::from_decimal(m, places).expect("in-range decimal must convert");
            assert_canonical(q);
            assert_eq!(rat(q), rat_of(m, den));
        }
    }
    // 0.85 exactly
    assert_eq!(rat(Q::from_decimal(85, 2).unwrap()), rat_of(85, 100));
    // > 18 places rejected
    assert!(Q::from_decimal(1, 19).is_none());
}

#[test]
fn from_f64_dir_matches_oracle() {
    let mut rng = Rng::new(0xF64);
    let mut converted = 0u32;
    for i in 0..20000 {
        // random bit patterns + structured edge cases
        let bits: u64 = match i {
            0 => 0,                          // +0.0
            1 => 0x8000_0000_0000_0000,      // -0.0
            2 => 0x0000_0000_0000_0001,      // min subnormal
            3 => 0x000F_FFFF_FFFF_FFFF,      // max subnormal
            4 => 0x0010_0000_0000_0000,      // min normal
            5 => 0x3FF0_0000_0000_0000,      // 1.0
            6 => 0x7FEF_FFFF_FFFF_FFFF,      // max finite
            7 => 0x7FF0_0000_0000_0000,      // +inf
            8 => 0x7FF8_0000_0000_0000,      // NaN
            _ => rng.next(),
        };
        let v = f64::from_bits(bits);
        for dir in DIRS {
            let r = Q::from_f64_dir(v, dir);
            if !v.is_finite() {
                assert!(r.is_none(), "NaN/inf must be rejected");
                continue;
            }
            let exact = Rational::try_from(v).expect("finite f64 is rational");
            match r {
                None => {
                    // rejected only when the integer magnitude exceeds MAX
                    assert!(
                        exact.clone().abs() > Rational::from(MAX_MAG),
                        "finite in-range f64 rejected: {v}"
                    );
                }
                Some(q) => {
                    converted += 1;
                    check_rounding_contract(q, &exact, dir, "from_f64");
                    // values on coarse grids convert exactly
                    if fits_budget(&exact) {
                        assert_eq!(rat(q), exact);
                    }
                }
            }
        }
    }
    assert!(converted > 1000, "test degenerated: too few conversions");
}

#[test]
fn to_f64_close_to_oracle() {
    let mut rng = Rng::new(0xD15);
    for _ in 0..5000 {
        let q = rand_q(&mut rng, 62, 62);
        let f = q.to_f64();
        assert!(f.is_finite());
        let back = Rational::try_from(f).unwrap();
        let exact = rat(q);
        let diff = (&back - &exact).abs();
        // <= ~4 ulp: comfortably 2^-50 relative
        let bound = rat_of(1, 1 << 50) * (exact.clone().abs() + Rational::from(1));
        assert!(diff <= bound, "to_f64 too far: {q:?} -> {f}");
    }
}

#[test]
fn constructors_match_oracle() {
    let mut rng = Rng::new(0xAB);
    for _ in 0..5000 {
        let n = rng.next() as i64;
        let d = rng.next() as i64;
        match Q::new(n, d) {
            None => {
                if d != 0 {
                    // must be a genuine budget overflow after reduction
                    let r = rat_of(n, d);
                    assert!(!fits_budget(&r), "constructor wrongly rejected {n}/{d}");
                }
            }
            Some(q) => {
                assert_canonical(q);
                assert_eq!(rat(q), rat_of(n, d));
            }
        }
    }
    assert!(Q::new(1, 0).is_none());
    assert!(Q::new(0, 0).is_none());
}
