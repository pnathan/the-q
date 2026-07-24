//! `serde` support (feature `serde`, spec §2.4): serialized as the
//! `(num, den)` integer pair -- an exact, lossless round-trip for any value
//! this crate itself produced, unlike any `f64` encoding. Deserialization
//! never trusts the wire form to already satisfy `I1`/`I2`: it goes through
//! [`Q::new`], which rejects `den == 0` and any pair whose reduced value
//! would exceed the `I2` budget, and canonicalizes everything else (so a
//! non-canonical but valid payload like `(2, 4)` still deserializes safely,
//! as `1/2`). This keeps the "structural equality == mathematical
//! equality" guarantee intact regardless of what a hand-crafted or foreign
//! payload looks like on the wire.

use crate::q::Q;
use serde::{de, Deserialize, Deserializer, Serialize, Serializer};

impl Serialize for Q {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        (self.numerator(), self.denominator()).serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for Q {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Q, D::Error> {
        let (num, den) = <(i64, i64)>::deserialize(deserializer)?;
        Q::new(num, den).ok_or_else(|| {
            de::Error::custom(format!(
                "not a canonical, in-budget Q: num={num}, den={den}"
            ))
        })
    }
}
