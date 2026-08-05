//! The `Rat` value type, the rounding-direction enum, and the width budget.
//!
//! The fields are public. Verus cannot state a public invariant about a
//! datatype whose fields it cannot see. See the note on [`Rat`]. Every
//! constructor establishes the invariant. Every operation preserves it. Under
//! Verus the invariant is a precondition of all of them. Thus a hand-built
//! value is inert. [`Rat::numerator`] and [`Rat::denominator`] are the
//! accessors.

use verus_builtin_macros::verus;

#[allow(unused_imports)]
use verus_builtin::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The magnitude budget: `2^62 - 1`.
///
/// Both `|num|` and `den` stay at or below this value. The bound is `2^62`
/// rather than `2^63` because of the widest intermediate in the crate,
/// `num1*den2 ± num2*den1`. That intermediate is bounded by
/// `2 * (2^62 - 1)^2 < 2^125`, which fits inside `i128`. A `2^63` budget pushes
/// the same intermediate to `2^127`, which overflows `i128::MAX = 2^127 - 1`.
pub const MAX_MAG: i64 = 4611686018427387903;  // 2^62 - 1

/// The largest decimal exponent accepted by `crate::q::Rat::from_decimal`.
///
/// `10^18 < 2^62 - 1 <= 10^19`. Eighteen places is therefore the last count
/// whose scale factor is itself representable.
pub const MAX_DEC_PLACES: u8 = 18;

/// Rounding direction for the operations that can round.
///
/// `Down` and `Up` are *directed*: they bracket the exact value (R2). This
/// bracketing lets [`crate::interval::QI`] be built without any new proofs.
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
/// Canonical form makes structural equality identical to mathematical equality.
/// Thus `PartialEq`/`Eq`/`Hash` are derivable-safe, and every value has exactly
/// one bit pattern. `Ord` is *not* derived. The derived lexicographic order on
/// `(num, den)` is not the order on rationals. `Ord` uses cross-multiplication
/// instead, and a proof shows that it agrees with the ghost order (V6).
///
/// # Why the fields are public
///
/// Verus treats a datatype as *opaque* wherever any of its fields is invisible.
/// A public specification must be well-formed everywhere it is visible. With
/// `pub(crate)` fields, `Rat::wf` cannot mention `self.num` at all. The type
/// invariant is then unstatable in the crate's public API.
///
/// One consequence is that `Rat { num: 3, den: 0 }` compiles. Such a value is
/// still not usable. **Every** operation in this crate `requires` `Rat::wf`.
/// Under Verus a hand-built value reaches no operation until the caller
/// discharges the invariant, and a malformed value cannot discharge it. In
/// unverified Rust the value is an ordinary hazard. Build values with
/// [`Rat::new`], [`Rat::from_decimal`] or [`Rat::from_int`]. These constructors
/// canonicalise and establish the invariant.
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
