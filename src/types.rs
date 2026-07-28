//! The `Q` value type, the rounding-direction enum, and the width budget.
//!
//! Fields are `pub(crate)`: the type invariant (canonical + bounded) is
//! maintained by every constructor and operation, and external code must not be
//! able to forge a non-canonical `Q`. Read access is via [`Q::numerator`] and
//! [`Q::denominator`].

use verus_builtin_macros::verus;

#[allow(unused_imports)]
use verus_builtin::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The magnitude budget: `2^62 - 1`.
///
/// Both `|num|` and `den` are held at or below this value. The bound is `2^62`
/// rather than `2^63` because the widest intermediate in the whole crate,
/// `num1*den2 ± num2*den1`, is bounded by `2 * (2^62 - 1)^2 < 2^125`, which is
/// comfortably inside `i128`. A `2^63` budget would push that intermediate to
/// `2^127`, overflowing `i128::MAX = 2^127 - 1`.
pub const MAX_MAG: i64 = 4611686018427387903;  // 2^62 - 1

/// The largest decimal exponent accepted by `crate::q::Q::from_decimal`.
///
/// `10^18 < 2^62 - 1 <= 10^19`, so eighteen places is the last one whose scale
/// factor is itself representable.
pub const MAX_DEC_PLACES: u8 = 18;

/// Rounding direction for the operations that can round.
///
/// `Down` and `Up` are *directed*: they bracket the exact value (R2), which is
/// what lets [`crate::interval::QI`] be built without any new proofs.
/// `Nearest` (ties to even) is the default for the plain operations.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Dir {
    /// Round toward `-inf`: the result is `<=` the exact value.
    Down,
    /// Round toward `+inf`: the result is `>=` the exact value.
    Up,
    /// Round to the nearest grid point; ties go to the even numerator.
    Nearest,
}

/// A bounded rational number, `num / den`.
///
/// # Invariants
///
/// Every value of this type satisfies (see [`crate::model`] for the formal
/// statement, and V1 in `VERIFICATION.md`):
///
/// * **I1 (canonical):** `den > 0`, `gcd(|num|, den) == 1` (hence `num == 0`
///   implies `den == 1`).
/// * **I2 (bounded):** `|num| <= MAX_MAG` and `den <= MAX_MAG`.
///
/// Canonical form makes structural equality identical to mathematical equality,
/// so `PartialEq`/`Eq`/`Hash` are derivable-safe and every value has exactly one
/// bit pattern. `Ord` is *not* derived — the derived lexicographic order on
/// `(num, den)` is not the order on rationals — it is implemented by
/// cross-multiplication and proven to agree with the ghost order (V6).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Q {
    pub(crate) num: i64,
    pub(crate) den: i64,
}

impl Q {
    /// The numerator of the canonical representation. Always coprime to
    /// [`Q::denominator`].
    pub fn numerator(&self) -> (r: i64)
        ensures r == self.num,
    {
        self.num
    }

    /// The denominator of the canonical representation. Always `>= 1`.
    pub fn denominator(&self) -> (r: i64)
        ensures r == self.den,
    {
        self.den
    }
}

} // verus!
