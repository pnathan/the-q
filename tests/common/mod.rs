//! Shared helpers for the differential / property test harness.
//!
//! The oracle is malachite-q (LGPL-3.0) — dev-dependency ONLY; CI enforces
//! that it never appears in the normal dependency tree.

#![allow(dead_code)]

use malachite_base::num::arithmetic::traits::Abs;
use malachite_q::Rational;
use the_q::{Dir, Q};

pub const MAX_MAG: i64 = 0x3FFF_FFFF_FFFF_FFFF; // 2^62 - 1

/// Deterministic xorshift64* PRNG — no rand dependency, reproducible runs.
pub struct Rng(pub u64);

impl Rng {
    pub fn new(seed: u64) -> Self {
        Rng(seed.max(1))
    }

    pub fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545F4914F6CDD1D)
    }

    pub fn i64_in(&mut self, lo: i64, hi: i64) -> i64 {
        let span = (hi - lo) as u64 + 1;
        lo + (self.next() % span) as i64
    }
}

/// The exact rational a `Q` denotes.
pub fn rat(q: Q) -> Rational {
    let (n, d) = q.to_parts();
    Rational::from_signeds(n, d)
}

/// Exact rational from a raw pair.
pub fn rat_of(n: i64, d: i64) -> Rational {
    Rational::from_signeds(n, d)
}

/// u64 gcd (test-local Euclid, independent of the crate under test).
pub fn gcd_u64(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        let r = a % b;
        a = b;
        b = r;
    }
    a
}

/// Assert the I1 + I2 invariants on the canonical fields.
pub fn assert_canonical(q: Q) {
    let (n, d) = q.to_parts();
    assert!(d > 0, "den must be positive: {q:?}");
    assert!(d <= MAX_MAG, "den over budget: {q:?}");
    assert!(n >= -MAX_MAG && n <= MAX_MAG, "num over budget: {q:?}");
    assert_eq!(gcd_u64(n.unsigned_abs(), d as u64), 1, "not coprime: {q:?}");
}

/// Does an exact rational fit the I2 budget (i.e. must the op be exact)?
pub fn fits_budget(r: &Rational) -> bool {
    use malachite_base::num::basic::traits::One;
    let num = r.to_numerator();
    let den = r.to_denominator();
    let _ = Rational::ONE; // keep the import honest
    u64::try_from(&num).map_or(false, |n| n <= MAX_MAG as u64)
        && u64::try_from(&den).map_or(false, |d| d <= MAX_MAG as u64)
}

/// |exact| <= MAX (the guard for R2/R3; beyond it the op saturates).
pub fn in_mag_range(r: &Rational) -> bool {
    r.clone().abs() <= Rational::from(MAX_MAG)
}

/// Check the full rounding contract of `got` against the exact value.
pub fn check_rounding_contract(got: Q, exact: &Rational, dir: Dir, ctx: &str) {
    assert_canonical(got);
    let got_r = rat(got);
    if fits_budget(exact) {
        // R1: identity on representables.
        assert_eq!(&got_r, exact, "R1 violated ({ctx}): got {got:?}, exact {exact}");
        return;
    }
    if !in_mag_range(exact) {
        // saturation: +-MAX/1
        let (n, d) = got.to_parts();
        assert_eq!(d, 1, "saturation den ({ctx})");
        assert_eq!(n.abs(), MAX_MAG, "saturation num ({ctx})");
        assert_eq!(n < 0, exact < &Rational::from(0), "saturation sign ({ctx})");
        return;
    }
    // R2: directed.
    match dir {
        Dir::Down => assert!(got_r <= *exact, "R2 Down violated ({ctx})"),
        Dir::Up => assert!(got_r >= *exact, "R2 Up violated ({ctx})"),
        Dir::Nearest => {}
    }
    // R3: |got - exact| <= 2^-60 * max(1, |exact|).
    let diff = (got_r - exact).abs();
    let eps = rat_of(1, 1 << 60);
    let exact_abs = exact.clone().abs();
    let bound = if exact_abs <= Rational::from(1) {
        eps
    } else {
        eps * exact_abs
    };
    assert!(diff <= bound, "R3 violated ({ctx}): diff {diff}, exact {exact}");
}

/// A random canonical Q with numerator/denominator up to the given bit sizes.
pub fn rand_q(rng: &mut Rng, num_bits: u32, den_bits: u32) -> Q {
    loop {
        let nmask = if num_bits >= 63 { i64::MAX } else { (1i64 << num_bits) - 1 };
        let dmask = if den_bits >= 63 { i64::MAX } else { (1i64 << den_bits) - 1 };
        let n = (rng.next() as i64) & nmask;
        let n = if rng.next() & 1 == 0 { n } else { -n };
        let d = ((rng.next() as i64) & dmask).max(1);
        if let Some(q) = Q::new(n, d) {
            return q;
        }
    }
}

/// A random Q in [0, 1] (the engine's opinion space).
pub fn rand_unit_q(rng: &mut Rng) -> Q {
    loop {
        let d = rng.i64_in(1, 1_000_000_000);
        let n = rng.i64_in(0, d);
        if let Some(q) = Q::new(n, d) {
            return q;
        }
    }
}

pub const DIRS: [Dir; 3] = [Dir::Down, Dir::Up, Dir::Nearest];
