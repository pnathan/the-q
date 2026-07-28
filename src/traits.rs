//! Unverified trait glue (enumerated in TRUSTED.md).
//!
//! Everything here is a thin delegate to a verified method or a direct
//! read of the canonical fields; no arithmetic happens in this module.
//! `PartialEq`/`Eq`/`Clone`/`Copy` are derived on the struct itself
//! (safe: canonical form makes structural equality mathematical equality,
//! proven by `lemma_canonical_unique`).
//!
//! Each impl is explicitly marked `#[verifier::external]` (under the
//! `verus_keep_ghost` cfg, so plain cargo builds are unaffected) - the
//! verification boundary is mechanical, not conventional: adding
//! arithmetic here would still compile, but the annotation makes the
//! unverified status visible at every item, not just in TRUSTED.md.

use crate::q::Q;

#[cfg_attr(verus_keep_ghost, verifier::external)]
impl core::hash::Hash for Q {
    // Canonical form: equal values have equal fields, so hashing fields
    // is consistent with the derived PartialEq.
    fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        let (n, d) = self.to_parts();
        n.hash(state);
        d.hash(state);
    }
}

#[cfg_attr(verus_keep_ghost, verifier::external)]
impl core::cmp::PartialOrd for Q {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.cmp_q(*other))
    }
}

#[cfg_attr(verus_keep_ghost, verifier::external)]
impl core::cmp::Ord for Q {
    // Delegates to the verified exact comparison `cmp_q` (i128
    // cross-multiplication; agrees with the ghost total order).
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.cmp_q(*other)
    }
}

#[cfg_attr(verus_keep_ghost, verifier::external)]
impl core::fmt::Display for Q {
    /// `"num/den"`.
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let (n, d) = self.to_parts();
        write!(f, "{}/{}", n, d)
    }
}

#[cfg_attr(verus_keep_ghost, verifier::external)]
impl core::fmt::Debug for Q {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let (n, d) = self.to_parts();
        write!(f, "Q({}/{})", n, d)
    }
}

#[cfg(feature = "serde")]
mod serde_impls {
    use crate::q::Q;
    use serde::de::Error;

    #[cfg_attr(verus_keep_ghost, verifier::external)]
    impl serde::Serialize for Q {
        /// Serializes as the exact `(num, den)` integer pair - exact
        /// round-trip, unlike any f64 encoding.
        fn serialize<S: serde::Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
            self.to_parts().serialize(s)
        }
    }

    #[cfg_attr(verus_keep_ghost, verifier::external)]
    impl<'de> serde::Deserialize<'de> for Q {
        /// Deserializes a `(num, den)` pair, re-canonicalizing through the
        /// verified constructor so the type invariant always holds (and
        /// rejecting `den == 0` / out-of-budget values).
        fn deserialize<D: serde::Deserializer<'de>>(d: D) -> Result<Q, D::Error> {
            let (n, den): (i64, i64) = serde::Deserialize::deserialize(d)?;
            Q::new(n, den).ok_or_else(|| {
                D::Error::custom("invalid Q: zero denominator or out of budget")
            })
        }
    }
}
