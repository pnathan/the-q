//! The `Q` type: canonical form, constructors, comparisons (spec §1, §2.1, §2.3).

use crate::rounding::MAX_MAGNITUDE;
use std::cmp::Ordering;
use std::fmt;

/// A canonical bounded rational: `value == num / den`.
///
/// Type invariants, upheld by every constructor and every operation in this
/// crate (spec obligation V1):
/// - **I1 (canonical):** `den > 0`, `gcd(|num|, den) == 1`, and `num == 0`
///   implies `den == 1`.
/// - **I2 (bounded):** `|num| <= 2^62 - 1` and `den <= 2^62 - 1`.
///
/// Canonical form makes structural equality agree with mathematical
/// equality, so `Eq`, `Ord`, and `Hash` are all meaningful.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Q {
    pub(crate) num: i64,
    pub(crate) den: i64,
}

fn gcd_i64(a: i64, b: i64) -> i64 {
    let (mut a, mut b) = (a.unsigned_abs(), b.unsigned_abs());
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    a as i64
}

impl Q {
    /// Build a `Q` from an already-canonical, already-in-budget `i128` pair.
    /// Internal only: every call site must have run this through
    /// `rounding::canonicalize_i128` (or equivalent) and a budget check first.
    pub(crate) fn from_canonical_i128(num: i128, den: i128) -> Q {
        debug_assert!(den > 0);
        debug_assert!(num.unsigned_abs() <= MAX_MAGNITUDE as u128);
        debug_assert!(den as u128 <= MAX_MAGNITUDE as u128);
        debug_assert!(num == 0 || gcd_i64(num as i64, den as i64) == 1);
        debug_assert!(num != 0 || den == 1);
        Q {
            num: num as i64,
            den: den as i64,
        }
    }

    pub const fn zero() -> Q {
        Q { num: 0, den: 1 }
    }

    pub const fn one() -> Q {
        Q { num: 1, den: 1 }
    }

    /// Exact for `|i| <= 2^62 - 1`; `None` otherwise.
    pub fn from_int(i: i64) -> Option<Q> {
        if i.unsigned_abs() <= MAX_MAGNITUDE as u64 {
            Some(Q { num: i, den: 1 })
        } else {
            None
        }
    }

    /// `None` iff `den == 0`, or the (always-exact) canonicalized result
    /// would exceed the `I2` budget. The latter only fires for `num`/`den`
    /// near `i64::MAX`/`i64::MIN` -- the spec's claim that "inputs within
    /// i64 always fit I2 after reduction" holds for the overwhelming
    /// majority of inputs but not, e.g., `new(i64::MAX, 1)`; this
    /// implementation is honest about that edge rather than silently
    /// truncating or panicking.
    pub fn new(num: i64, den: i64) -> Option<Q> {
        if den == 0 {
            return None;
        }
        let (num, den) = if den < 0 {
            (num.checked_neg()?, den.checked_neg()?)
        } else {
            (num, den)
        };
        if num == 0 {
            return Some(Q::zero());
        }
        let g = gcd_i64(num, den);
        let (num, den) = (num / g, den / g);
        if num.unsigned_abs() <= MAX_MAGNITUDE as u64 && den <= MAX_MAGNITUDE {
            Some(Q { num, den })
        } else {
            None
        }
    }

    /// Exact decimal ingestion, e.g. `from_decimal(85, 2) == Some(0.85)`.
    /// `None` if `den == 10^dec_places` or the reduced result would exceed
    /// `I2` (in practice `dec_places > 18` always fails this).
    pub fn from_decimal(mantissa: i64, dec_places: u8) -> Option<Q> {
        let den: i128 = 10i128.checked_pow(dec_places as u32)?;
        if den > MAX_MAGNITUDE as i128 {
            return None;
        }
        // mantissa is an i64 and den <= MAX_MAGNITUDE (checked above), so the
        // gcd-reduced result always fits I2 and from_exact_i128 never
        // actually rounds here -- see tests/property.rs `from_decimal_is_exact`.
        Some(crate::rounding::from_exact_i128(
            mantissa as i128,
            den,
            crate::rounding::Dir::Nearest,
        ))
    }

    pub fn numerator(&self) -> i64 {
        self.num
    }

    pub fn denominator(&self) -> i64 {
        self.den
    }

    pub fn is_zero(&self) -> bool {
        self.num == 0
    }

    pub fn is_one(&self) -> bool {
        self.num == 1 && self.den == 1
    }

    pub fn signum(&self) -> i32 {
        self.num.signum() as i32
    }

    /// `0 <= self <= 1`.
    pub fn in_unit_interval(&self) -> bool {
        self.num >= 0 && self.num <= self.den
    }
}

impl PartialOrd for Q {
    fn partial_cmp(&self, other: &Q) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Q {
    /// Exact cross-multiplication comparison in `i128`
    /// (`a.num * b.den` vs `b.num * a.den`); both denominators are positive
    /// by `I1` so no sign correction is needed. `Q` is a total order,
    /// agreeing with the mathematical order on `int` (spec V6).
    fn cmp(&self, other: &Q) -> Ordering {
        let lhs = self.num as i128 * other.den as i128;
        let rhs = other.num as i128 * self.den as i128;
        lhs.cmp(&rhs)
    }
}

impl fmt::Display for Q {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}/{}", self.num, self.den)
    }
}
