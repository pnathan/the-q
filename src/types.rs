//! The `Rat` value type, the rounding-direction enum, and the width budget.
//!
//! The representation is private to this module. Every public constructor
//! establishes the invariant, every operation preserves it, and downstream
//! callers inspect values through [`Rat::numerator`] and [`Rat::denominator`].

use verus_builtin_macros::verus;

#[allow(unused_imports)]
use verus_builtin::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The magnitude budget, `2^62 − 1`: the largest under which
/// `num1·den2 ± num2·den1 < 2^125` fits `i128`.
pub const MAX_MAG: i64 = 4611686018427387903;  // 2^62 - 1

/// The largest decimal exponent accepted by `crate::q::Rat::from_decimal`.
///
/// `10^18 < 2^62 - 1 <= 10^19`. Eighteen places is therefore the last count
/// whose scale factor is itself representable.
pub const MAX_DEC_PLACES: u8 = 18;

/// The largest scale (digits after the point) a `rust_decimal::Decimal`
/// carries. `crate::convert::from_decimal128_dir` accepts exactly the domain
/// `Decimal` itself guarantees: `scale() <= MAX_DECIMAL_SCALE` and
/// `|mantissa()| <= MAX_DECIMAL_MANTISSA`.
pub const MAX_DECIMAL_SCALE: u32 = 28;

/// `2^96 - 1`, the largest magnitude a `rust_decimal::Decimal` mantissa
/// carries (a 96-bit unsigned integer with the sign held separately).
pub const MAX_DECIMAL_MANTISSA: i128 = 79228162514264337593543950335;

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

/// A bounded rational `num / den`: canonical (`den > 0`, `gcd(|num|, den) == 1`)
/// and bounded (`|num|, den <= MAX_MAG`), so structural equality is value
/// equality and `Eq`/`Hash` derive safely. `Ord` is hand-written by
/// cross-multiplication. The fields are private:
///
/// ```compile_fail
/// use the_q::Rat;
/// let _ = Rat { num: 1, den: 2 };
/// ```
///
/// ```compile_fail
/// use the_q::Rat;
/// let mut r = Rat::one();
/// r.den = 0;
/// ```
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Rat {
    /// The numerator. Coprime to `den`; `|num| <= MAX_MAG`.
    num: i64,
    /// The denominator. Strictly positive; `den <= MAX_MAG`.
    den: i64,
}

impl Rat {
    /// The numerator, as an unbounded integer.
    pub closed spec fn n(self) -> int {
        self.num as int
    }

    /// The denominator, as an unbounded integer.
    pub closed spec fn d(self) -> int {
        self.den as int
    }

    /// Ghost-only constructor used by public specifications. Its closed body
    /// keeps the crate-private representation out of public open contracts.
    pub closed spec fn from_raw_spec(num: i64, den: i64) -> Rat {
        Rat { num, den }
    }

    /// Exposes the modeled components of [`Rat::from_raw_spec`] without
    /// exposing the representation fields themselves.
    pub proof fn lemma_from_raw_spec_components(num: i64, den: i64)
        ensures
            Rat::from_raw_spec(num, den).n() == num as int,
            Rat::from_raw_spec(num, den).d() == den as int,
    {
        reveal(Rat::from_raw_spec);
        reveal(Rat::n);
        reveal(Rat::d);
    }

    /// Two rationals with identical abstract components are the same value.
    pub proof fn lemma_extensional(a: Rat, b: Rat)
        requires
            a.n() == b.n(),
            a.d() == b.d(),
        ensures
            a == b,
    {
        reveal(Rat::n);
        reveal(Rat::d);
    }

    /// Internal representation constructor. Callers must establish any
    /// well-formedness property required by their public contract.
    pub(crate) fn from_raw_parts(num: i64, den: i64) -> (r: Rat)
        ensures
            r == Rat::from_raw_spec(num, den),
            r.n() == num as int,
            r.d() == den as int,
    {
        proof {
            reveal(Rat::from_raw_spec);
            reveal(Rat::n);
            reveal(Rat::d);
        }
        Rat { num, den }
    }

    /// The numerator of the canonical representation. Always coprime to
    /// [`Rat::denominator`].
    ///
    /// ```
    /// use the_q::Rat;
    ///
    /// let r = Rat::new(-3, 6).unwrap();
    /// assert_eq!(r.numerator(), -1);
    /// assert_eq!(r.denominator(), 2);
    /// ```
    pub fn numerator(&self) -> (r: i64)
        ensures r as int == self.n(),
    {
        self.num
    }

    /// The denominator of the canonical representation. Always `>= 1`.
    ///
    /// ```
    /// use the_q::Rat;
    ///
    /// let r = Rat::new(3, 6).unwrap();
    /// assert_eq!(r.denominator(), 2);
    /// assert_eq!(Rat::one().denominator(), 1);
    /// ```
    pub fn denominator(&self) -> (r: i64)
        ensures r as int == self.d(),
    {
        self.den
    }
}

} // verus!
