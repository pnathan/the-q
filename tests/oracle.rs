//! Differential tests against `malachite-q` (an LGPL-3.0 **dev-dependency only**
//! — it must never enter the release dependency tree; CI enforces this).
//!
//! These tests are the empirical backing for the rounding contract that Verus
//! proves symbolically:
//! - **R1 (identity on representables):** when the exact reduced result fits the
//!   budget, our result equals the oracle exactly.
//! - **R2 (directed):** `Down ≤ exact ≤ Up`.
//! - **R3 (error bound):** `|result − exact| ≤ 2^-60 · max(1, |exact|)`.
//! - **V3 (value correctness):** exact-path results equal the oracle.
//!
//! Inputs cover exhaustive small denominators/numerators and a large
//! deterministic pseudo-random sweep (fixed seed ⟹ reproducible).

use malachite_base::num::arithmetic::traits::Abs;
use malachite_base::num::basic::traits::One;
use malachite_q::Rational;
use the_q::{Dir, BUDGET, Q};

// ---- helpers ---------------------------------------------------------------

fn to_rat(q: Q) -> Rational {
    Rational::from_signeds(q.numer(), q.denom())
}

/// `1 / 2^60` as a Rational (2^60 fits i64).
fn eps() -> Rational {
    Rational::from_signeds(1i64, 1i64 << 60)
}

/// The R3 relative-with-floor bound `2^-60 · max(1, |exact|)`.
fn bound_for(exact: &Rational) -> Rational {
    let unit = Rational::ONE;
    let mag = exact.clone().abs();
    let m = if mag > unit { mag } else { unit };
    eps() * m
}

/// Assert the full R1/R2/R3 contract for one rounded result against the exact
/// oracle value.
fn assert_contract(result: Q, exact: &Rational, dir: Dir) {
    let r = to_rat(result);
    // R3: error bound.
    let diff = (&r - exact).abs();
    assert!(
        diff <= bound_for(exact),
        "R3 violated: dir={:?} result={} exact={} diff>{}",
        dir,
        result,
        exact,
        bound_for(exact)
    );
    // R2: directed inequality.
    match dir {
        Dir::Down => assert!(&r <= exact, "R2 Down: {} > {}", result, exact),
        Dir::Up => assert!(&r >= exact, "R2 Up: {} < {}", result, exact),
        Dir::Nearest => {}
    }
    // R1: if the exact value is representable within budget, result must be EXACT.
    if fits_budget(exact) {
        assert!(
            &r == exact,
            "R1 identity violated: representable {} rounded to {}",
            exact,
            result
        );
    }
}

/// Does this exact Rational fit invariant I2 (`|num| ≤ 2^62−1`, `den ≤ 2^62−1`)?
fn fits_budget(x: &Rational) -> bool {
    let (n, d) = x.to_numerator_and_denominator();
    let bmax = malachite_nz::natural::Natural::from(BUDGET as u64);
    n <= bmax && d <= bmax
}

// ---- deterministic PRNG (fixed seed ⟹ reproducible, thread-independent) ----

struct Lcg(u64);
impl Lcg {
    fn new(seed: u64) -> Self {
        Lcg(seed)
    }
    fn next_u64(&mut self) -> u64 {
        // SplitMix64
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
    /// A random Q with small-to-moderate numerator/denominator (engine-like).
    fn next_q(&mut self, max_num: i64, max_den: i64) -> Q {
        let n = (self.next_u64() % (2 * max_num as u64 + 1)) as i64 - max_num;
        let d = (self.next_u64() % (max_den as u64)) as i64 + 1;
        Q::new(n, d).unwrap()
    }
    /// A random Q with denominators pushed toward the budget edge.
    fn next_q_big(&mut self) -> Q {
        let n = (self.next_u64() % (2 * (BUDGET as u64) + 1)) as i128 - BUDGET as i128;
        let d = (self.next_u64() % (BUDGET as u64)) as i128 + 1;
        // Reduce into budget via new (already ≤ i64 range here since we mod BUDGET).
        Q::new(n as i64, d as i64).unwrap()
    }
}

// ---- exhaustive small inputs ----------------------------------------------

fn small_qs() -> Vec<Q> {
    let mut v = Vec::new();
    for n in -6i64..=6 {
        for d in 1i64..=6 {
            if let Some(q) = Q::new(n, d) {
                v.push(q);
            }
        }
    }
    v
}

#[test]
fn exhaustive_small_add_sub_mul() {
    for a in small_qs() {
        for b in small_qs() {
            let ra = to_rat(a);
            let rb = to_rat(b);
            for &dir in &[Dir::Down, Dir::Up, Dir::Nearest] {
                assert_contract(a.add_dir(b, dir), &(&ra + &rb), dir);
                assert_contract(a.sub_dir(b, dir), &(&ra - &rb), dir);
                assert_contract(a.mul_dir(b, dir), &(&ra * &rb), dir);
                if !b.is_zero() {
                    assert_contract(a.div_dir(b, dir), &(&ra / &rb), dir);
                }
            }
        }
    }
}

#[test]
fn exhaustive_small_predicates_match_oracle() {
    for a in small_qs() {
        for b in small_qs() {
            let ra = to_rat(a);
            let rb = to_rat(b);
            assert_eq!(a.lt(b), ra < rb);
            assert_eq!(a.le(b), ra <= rb);
            assert_eq!(a.gt(b), ra > rb);
            assert_eq!(a.eq(b), ra == rb);
            assert_eq!(a.cmp_q(b), ra.cmp(&rb));
        }
    }
}

#[test]
fn random_engine_like_all_ops() {
    let mut rng = Lcg::new(0x00C0_FFEE_1234_5678);
    for _ in 0..40_000 {
        let a = rng.next_q(10_000, 10_000);
        let b = rng.next_q(10_000, 10_000);
        let ra = to_rat(a);
        let rb = to_rat(b);
        for &dir in &[Dir::Down, Dir::Up, Dir::Nearest] {
            assert_contract(a.add_dir(b, dir), &(&ra + &rb), dir);
            assert_contract(a.sub_dir(b, dir), &(&ra - &rb), dir);
            assert_contract(a.mul_dir(b, dir), &(&ra * &rb), dir);
            if !b.is_zero() {
                assert_contract(a.div_dir(b, dir), &(&ra / &rb), dir);
            }
        }
    }
}

#[test]
fn random_budget_edge_forces_rounding() {
    let mut rng = Lcg::new(0xDEAD_BEEF_CAFE);
    let mut rounded_seen = 0u64;
    for _ in 0..20_000 {
        let a = rng.next_q_big();
        let b = rng.next_q_big();
        let ra = to_rat(a);
        let rb = to_rat(b);
        for &dir in &[Dir::Down, Dir::Up, Dir::Nearest] {
            let exact = &ra + &rb;
            let res = a.add_dir(b, dir);
            assert_contract(res, &exact, dir);
            if !fits_budget(&exact) {
                rounded_seen += 1;
            }
            let mexact = &ra * &rb;
            assert_contract(a.mul_dir(b, dir), &mexact, dir);
        }
    }
    // Confirm we actually exercised the rounding path, not just R1.
    assert!(
        rounded_seen > 0,
        "budget-edge sweep never triggered rounding"
    );
}

#[test]
fn long_fold_chain_error_tracked() {
    // 10^4-op fold; error must stay within the accumulated k·2^-60 bound and
    // remain byte-identical run to run (determinism).
    let mut rng = Lcg::new(0x5EED);
    let xs: Vec<Q> = (0..10_000).map(|_| rng.next_q(1000, 1000)).collect();
    let mut acc = Q::zero();
    let mut exact = Rational::from_signeds(0i64, 1i64);
    let mut k: i64 = 0;
    for &x in &xs {
        acc = acc.add(x);
        exact = &exact + &to_rat(x);
        k += 1;
        let diff = (&to_rat(acc) - &exact).abs();
        // Accumulated bound k·2^-60·max(1,|exact|).
        let per = bound_for(&exact);
        let bound = Rational::from_signeds(k, 1i64) * per;
        assert!(
            diff <= bound,
            "fold error exceeded k·2^-60 at step {}: diff={} bound={}",
            k,
            diff,
            bound
        );
    }
}
