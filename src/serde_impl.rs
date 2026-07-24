// Serde: serialize Q as (num, den) integer pair — exact round-trip.
// Never encode as f64 (loses precision and round-trip guarantee).

use serde::{Deserialize, Deserializer, Serialize, Serializer};
use crate::q::Q;

#[derive(Serialize, Deserialize)]
struct QSerde {
    num: i64,
    den: i64,
}

impl Serialize for Q {
    fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        QSerde { num: self.num, den: self.den }.serialize(s)
    }
}

impl<'de> Deserialize<'de> for Q {
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        let QSerde { num, den } = QSerde::deserialize(d)?;
        Q::new(num, den).ok_or_else(|| serde::de::Error::custom("invalid Q: den==0"))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn serde_roundtrip() {
        let q = Q::new(3, 4).unwrap();
        let json = serde_json::to_string(&q).unwrap();
        let q2: Q = serde_json::from_str(&json).unwrap();
        assert_eq!(q, q2);
    }
}
