//! The `Rat` value type, the rounding-direction enum, and the width budget.
//!
//! The fields are public — Verus cannot state a public invariant about a
//! datatype whose fields it cannot see (see the note on [`Rat`]). The invariant
//! is established by every constructor and preserved by every operation, and
//! under Verus it is a precondition of all of them, so a hand-built value is
//! inert. [`Rat::numerator`] and [`Rat::denominator`] are the intended accessors.

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

/// The largest decimal exponent accepted by `crate::q::Rat::from_decimal`.
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
///
/// # Why the fields are public
///
/// Verus treats a datatype as *opaque* wherever any of its fields is invisible,
/// and a public specification must be well-formed everywhere it is visible. With
/// `pub(crate)` fields, `Rat::wf` could not so much as mention `self.num` — the
/// type invariant would be unstatable in the crate's public API.
///
/// The practical consequence is that `Rat { num: 3, den: 0 }` compiles. It is
/// still not usable: **every** operation in this crate `requires` `Rat::wf`, so
/// under Verus a hand-built value cannot be passed to anything until the caller
/// discharges the invariant — which a malformed one cannot do. In unverified
/// Rust it is an ordinary footgun. Build values with [`Rat::new`],
/// [`Rat::from_decimal`] or [`Rat::from_int`], which canonicalise and establish the
/// invariant for you.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Rat {
    /// The numerator. Coprime to `den`; `|num| <= MAX_MAG`.
    pub num: i64,
    /// The denominator. Strictly positive; `den <= MAX_MAG`.
    pub den: i64,
}

impl Rat {
    /// The numerator of the canonical representation. Always coprime to
    /// [`Rat::denominator`].
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
