//! `convert::from_ratio128_dir`/`from_ratio128_exact`, the shared `(n, d)`
//! ingestion core every external-library adapter in `convert.rs` is built on
//! (issue #33 follow-up). These check it directly, against `Rat::new_rounded`
//! (its `i64`-only sibling) and against the oracle, rather than only through
//! whichever library happens to call it.

mod common;

use common::*;
use the_q::{Dir, Rat, from_ratio128_dir, from_ratio128_exact};

#[test]
fn agrees_with_new_rounded_on_i64_pairs() {
    let mut rng = Rng::new(0xBADA_5510_ABCD_0033);
    for _ in 0..5_000 {
        let n = rng.next_u64() as i64;
        let d = rng.next_u64() as i64;
        if d == 0 {
            continue;
        }
        for dir in [Dir::Down, Dir::Up, Dir::Nearest] {
            let via_ratio = from_ratio128_dir(n as i128, d as i128, dir).unwrap();
            let via_new_rounded = Rat::new_rounded(n, d, dir).unwrap();
            assert_eq!(via_ratio, via_new_rounded, "n={n}, d={d}, dir={dir:?}");
        }
    }
}

#[test]
fn zero_denominator_is_none() {
    assert_eq!(from_ratio128_dir(1, 0, Dir::Nearest), None);
    assert_eq!(from_ratio128_exact(1, 0), None);
}

#[test]
fn negative_denominator_folds_its_sign_onto_the_numerator() {
    // -3 / -4 == 3 / 4, not -(3/4).
    let r = from_ratio128_dir(-3, -4, Dir::Nearest).unwrap();
    assert_eq!(r, Rat::new(3, 4).unwrap());
    let r = from_ratio128_dir(3, -4, Dir::Nearest).unwrap();
    assert_eq!(r, Rat::new(-3, 4).unwrap());
}

#[test]
fn out_of_range_magnitudes_are_none() {
    const N_LIMIT: i128 = 85_070_591_730_234_615_865_843_651_857_942_052_863;
    const D_LIMIT: i128 = 21_267_647_932_558_653_966_460_912_964_485_513_216;
    assert!(from_ratio128_dir(N_LIMIT, 1, Dir::Nearest).is_some());
    assert_eq!(from_ratio128_dir(N_LIMIT + 1, 1, Dir::Nearest), None);
    assert!(from_ratio128_dir(1, D_LIMIT, Dir::Nearest).is_some());
    assert_eq!(from_ratio128_dir(1, D_LIMIT + 1, Dir::Nearest), None);
    // i128::MIN would overflow on negation if bound-checked after the sign
    // flip instead of before it; this must not panic, and must be refused.
    assert_eq!(from_ratio128_dir(i128::MIN, 1, Dir::Nearest), None);
    assert_eq!(from_ratio128_dir(1, i128::MIN, Dir::Nearest), None);
    assert_eq!(from_ratio128_exact(i128::MIN, 1), None);
}

#[test]
fn exact_refuses_what_dir_would_round() {
    // A denominator just past MAX_MAG, coprime to the numerator: on the
    // R2/R3 snap path, not the exact one.
    let n: i128 = 1;
    let d: i128 = 4_611_686_018_427_387_904 + 1; // MAX_MAG + 2, odd distance from n
    assert_eq!(from_ratio128_exact(n, d), None);
    assert!(from_ratio128_dir(n, d, Dir::Nearest).is_some());
}

#[test]
fn exact_matches_new_rounded_when_it_fits() {
    // `i32` magnitude, not `i64`: `i64::MAX` alone already exceeds `MAX_MAG`
    // (`2^62 - 1`), so an `i64/i64` pair is not guaranteed exact in general.
    // Bounding to `i32` keeps every reduced pair far inside the budget, so
    // this is always on the exact path.
    let mut rng = Rng::new(0xFACE_FEED_0033_0001);
    for _ in 0..5_000 {
        let n = rng.next_u64() as i32 as i64;
        let d = ((rng.next_u64() as i32).saturating_abs() as i64).wrapping_add(1);
        let via_ratio_exact = from_ratio128_exact(n as i128, d as i128);
        let via_new_rounded = Rat::new_rounded(n, d, Dir::Nearest).unwrap();
        assert_eq!(via_ratio_exact, Some(via_new_rounded), "n={n}, d={d}");
    }
}
