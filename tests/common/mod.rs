//! Shared oracle plumbing for the differential test suites.
//!
//! `malachite-q` is the oracle: arbitrary-precision, exact, and completely
//! independent of anything in this crate. It is a **dev-dependency only** —
//! LGPL-3.0-only is fine for test code that is never distributed, and
//! `scripts/check-no-lgpl.sh` fails CI if it ever leaks into the shipped
//! dependency tree.

#![allow(dead_code)]

use malachite_q::Rational;
use the_q::{Dir, MAX_MAG, Rat};

/// `Rat` as an exact oracle rational.
pub fn rat(q: Rat) -> Rational {
    Rational::from_signeds(q.numerator() as i128, q.denominator() as i128)
}

/// An exact oracle rational from an `i128` pair.
pub fn rat_of(n: i128, d: i128) -> Rational {
    Rational::from_signeds(n, d)
}

/// `0` as an oracle rational.
pub fn zero() -> Rational {
    Rational::from_signeds(0i128, 1i128)
}

/// `1` as an oracle rational.
pub fn one() -> Rational {
    Rational::from_signeds(1i128, 1i128)
}

/// `|x|` on the oracle type.
pub fn rabs(x: Rational) -> Rational {
    if x < zero() { -x } else { x }
}

/// `2^61`, the R3 precision unit. The specification's bar is `B >= 60`; the
/// implementation achieves 61, and the differential suite pins the stronger
/// bound so a regression to `60` fails here rather than passing quietly.
pub fn two_pow_b() -> Rational {
    Rational::from_signeds(1i128 << 61, 1i128)
}

/// `MAX_MAG` as an oracle rational.
pub fn max_mag_rat() -> Rational {
    Rational::from_signeds(MAX_MAG as i128, 1i128)
}

/// Does the exact value reduce to something inside the budget (I2)?
///
/// This is the oracle's own answer to "should R1 have applied?", computed
/// entirely independently of `the-q`'s reduction code.
pub fn fits_budget(r: &Rational) -> bool {
    let (n, d) = r.to_numerator_and_denominator();
    let max = malachite_nz::natural::Natural::from(MAX_MAG as u64);
    n <= max && d <= max
}

/// Is the exact value representable at all (`|value| <= MAX_MAG`)?
pub fn magnitude_fits(r: &Rational) -> bool {
    rabs(r.clone()) <= max_mag_rat()
}

/// Assert the R3 error bound: `|result - exact| * 2^61 <= max(1, |exact|)`.
pub fn assert_r3(result: Rat, exact: &Rational, what: &str) {
    let got = rat(result);
    let err = rabs(got.clone() - exact.clone());
    let bound = if rabs(exact.clone()) > one() {
        rabs(exact.clone())
    } else {
        one()
    };
    assert!(
        err * two_pow_b() <= bound,
        "R3 violated for {what}: got {got}, exact {exact}"
    );
}

/// Assert R1: on the exact path the operation must be bit-exact.
pub fn assert_exact_if_representable(result: Rat, exact: &Rational, what: &str) {
    if fits_budget(exact) {
        assert_eq!(
            rat(result),
            *exact,
            "R1 violated for {what}: exact value {exact} is representable but got {}",
            rat(result)
        );
    }
}

/// Assert R2: `Down <= exact <= Up`.
pub fn assert_r2(down: Rat, up: Rat, exact: &Rational, what: &str) {
    assert!(
        rat(down) <= *exact,
        "R2 (Down) violated for {what}: {} > {exact}",
        rat(down)
    );
    assert!(
        rat(up) >= *exact,
        "R2 (Up) violated for {what}: {} < {exact}",
        rat(up)
    );
}

/// Assert the type invariant I1 + I2 on a value the library produced.
///
/// The library's own proofs say this always holds; the test checks it anyway,
/// because a proof that has not been run is a hypothesis.
pub fn assert_wf(q: Rat, what: &str) {
    let (n, d) = (q.numerator(), q.denominator());
    assert!(d > 0, "I1 violated ({what}): den {d} <= 0");
    assert!(d <= MAX_MAG, "I2 violated ({what}): den {d} > MAX_MAG");
    assert!(
        n.unsigned_abs() <= MAX_MAG as u64,
        "I2 violated ({what}): |num| {n} > MAX_MAG"
    );
    if n == 0 {
        assert_eq!(d, 1, "I1 violated ({what}): zero with den {d}");
    }
    assert_eq!(
        gcd_u64(n.unsigned_abs(), d as u64),
        1,
        "I1 violated ({what}): {n}/{d} is not in lowest terms"
    );
}

/// An independent gcd for the invariant check — deliberately not the crate's.
pub fn gcd_u64(a: u64, b: u64) -> u64 {
    let (mut x, mut y) = (a, b);
    while y != 0 {
        let t = x % y;
        x = y;
        y = t;
    }
    x
}

/// A deterministic xorshift64* PRNG.
///
/// Deliberately not the `rand` crate: the test suite must produce byte-identical
/// results on every machine and every run, so that a failure can be reproduced
/// from the seed alone.
pub struct Rng(u64);

impl Rng {
    pub fn new(seed: u64) -> Rng {
        Rng(seed | 1)
    }

    pub fn next_u64(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }

    pub fn below(&mut self, n: u64) -> u64 {
        self.next_u64() % n
    }

    /// A `Rat` drawn from a mixture of magnitude classes: tiny denominators
    /// (the engine's usual case), short decimals, mid-range, and values right
    /// at the budget edge.
    pub fn q(&mut self) -> Rat {
        loop {
            let class = self.below(6);
            let (n, d): (i64, i64) = match class {
                0 => (self.below(21) as i64 - 10, self.below(10) as i64 + 1),
                1 => (self.below(10001) as i64 - 5000, 10000),
                2 => (
                    self.below(1 << 20) as i64 - (1 << 19),
                    self.below(1 << 20) as i64 + 1,
                ),
                3 => (
                    self.below(1 << 40) as i64 - (1 << 39),
                    self.below(1 << 40) as i64 + 1,
                ),
                4 => (
                    (self.next_u64() % (MAX_MAG as u64)) as i64,
                    (self.next_u64() % (MAX_MAG as u64)) as i64 + 1,
                ),
                _ => (
                    MAX_MAG - self.below(4) as i64,
                    MAX_MAG - self.below(4) as i64,
                ),
            };
            if let Some(q) = Rat::new(n, d) {
                return q;
            }
        }
    }

    /// A non-zero `Rat`, for division and reciprocal tests.
    pub fn q_nonzero(&mut self) -> Rat {
        loop {
            let q = self.q();
            if !q.is_zero() {
                return q;
            }
        }
    }

    /// A `Rat` in `[0, 1]` — the engine's actual working domain.
    pub fn q_unit(&mut self) -> Rat {
        loop {
            let d = self.below(1 << 30) as i64 + 1;
            let n = self.below(d as u64 + 1) as i64;
            if let Some(q) = Rat::new(n, d) {
                return q;
            }
        }
    }
}

/// All three rounding directions.
pub const DIRS: [Dir; 3] = [Dir::Down, Dir::Up, Dir::Nearest];
