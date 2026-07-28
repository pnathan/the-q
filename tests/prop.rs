//! Property tests (proptest, with shrinking) focused on the trusted
//! boundary where the Verus proofs do not reach: `to_f64`, the
//! `f64::to_bits` bridge behind `from_f64_dir`, and the unverified trait
//! glue. Shrinking gives minimal counterexamples if the trusted
//! assumptions are ever wrong.

mod common;

use common::*;
use malachite_base::num::arithmetic::traits::Abs;
use malachite_q::Rational;
use proptest::prelude::*;
use the_q::{Dir, Q};

fn arb_q() -> impl Strategy<Value = Q> {
    (any::<i64>(), any::<i64>().prop_filter("nonzero den", |d| *d != 0))
        .prop_filter_map("in budget", |(n, d)| Q::new(n, d))
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(2000))]

    /// to_f64 (external_body) stays within a few ulp of the exact value.
    #[test]
    fn prop_to_f64_close(q in arb_q()) {
        let f = q.to_f64();
        prop_assert!(f.is_finite());
        let back = Rational::try_from(f).unwrap();
        let exact = rat(q);
        let diff = (&back - &exact).abs();
        let bound = rat_of(1, 1 << 50) * (exact.clone().abs() + Rational::from(1));
        prop_assert!(diff <= bound, "to_f64 too far for {q:?} -> {f}");
    }

    /// from_f64_dir (to_bits bridge + verified decode) meets the rounding
    /// contract against the exact rational of arbitrary bit patterns.
    #[test]
    fn prop_from_f64_contract(bits in any::<u64>(), dir_ix in 0usize..3) {
        let v = f64::from_bits(bits);
        let dir = DIRS[dir_ix];
        match Q::from_f64_dir(v, dir) {
            None => {
                if v.is_finite() {
                    let exact = Rational::try_from(v).unwrap();
                    prop_assert!(
                        exact.clone().abs() > Rational::from(MAX_MAG),
                        "in-range finite f64 rejected: {v}"
                    );
                }
            }
            Some(q) => {
                prop_assert!(v.is_finite());
                let exact = Rational::try_from(v).unwrap();
                check_rounding_contract(q, &exact, dir, "prop_from_f64");
            }
        }
    }

    /// Round-trip: values already on a representable dyadic grid convert
    /// back exactly through the trusted boundary.
    #[test]
    fn prop_f64_dyadic_round_trip(mant in -(1i64 << 50)..(1i64 << 50), shift in 0u32..40) {
        let v = (mant as f64) / (1u64 << shift) as f64;
        let q = Q::from_f64_dir(v, Dir::Nearest).unwrap();
        prop_assert_eq!(rat(q), Rational::try_from(v).unwrap());
        // and back out within to_f64's tolerance (exact here: |v| < 2^53)
        prop_assert_eq!(q.to_f64(), v);
    }

    /// Constructor canonicality + Ord glue consistency (unverified trait
    /// delegation) against the oracle order.
    #[test]
    fn prop_ord_glue_matches_oracle(a in arb_q(), b in arb_q()) {
        assert_canonical(a);
        prop_assert_eq!(a.cmp(&b), rat(a).cmp(&rat(b)));
        prop_assert_eq!(a == b, rat(a) == rat(b));
    }
}
