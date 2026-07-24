//! Arithmetic, min/max/clamp (spec §2.2).
//!
//! Every op computes its exact result in `i128` and funnels it through
//! [`crate::rounding::from_exact_i128`], which is exact whenever the
//! reduced result fits the budget (R1) and directed-rounds otherwise
//! (R2-R4). See the overflow-safety table in the crate README / spec §1 for
//! why `i128` is sufficient headroom for every op below given `I2`-bounded
//! inputs (`|num|, den <= 2^62 - 1`):
//!
//! | op       | worst intermediate            | bound          |
//! |----------|--------------------------------|----------------|
//! | mul      | `num1*num2`, `den1*den2`       | `< 2^124`      |
//! | add/sub  | `num1*den2 +/- num2*den1`      | `< 2^125`      |
//! | add/sub  | `den1*den2`                    | `< 2^124`      |
//!
//! `add`/`mul` are commutative unconditionally; associativity and
//! distributivity hold only on the exact (unrounded) path -- rounding
//! breaks them in general, by design (spec §3, "honesty consequence").
//! `tests/property.rs` checks commutativity always and associativity only
//! for small, budget-representable inputs.

use crate::q::Q;
use crate::rounding::{from_exact_i128, Dir};

pub fn add(a: Q, b: Q) -> Q {
    let num = a.numerator() as i128 * b.denominator() as i128
        + b.numerator() as i128 * a.denominator() as i128;
    let den = a.denominator() as i128 * b.denominator() as i128;
    from_exact_i128(num, den, Dir::Nearest)
}

pub fn sub(a: Q, b: Q) -> Q {
    let num = a.numerator() as i128 * b.denominator() as i128
        - b.numerator() as i128 * a.denominator() as i128;
    let den = a.denominator() as i128 * b.denominator() as i128;
    from_exact_i128(num, den, Dir::Nearest)
}

pub fn mul(a: Q, b: Q) -> Q {
    let num = a.numerator() as i128 * b.numerator() as i128;
    let den = a.denominator() as i128 * b.denominator() as i128;
    from_exact_i128(num, den, Dir::Nearest)
}

/// Requires `!b.is_zero()`. In the absence of a Verus-discharged static
/// precondition, this is enforced as a hard runtime panic (in every build
/// profile, not just debug) rather than silently producing an invalid `Q`.
pub fn div(a: Q, b: Q) -> Q {
    assert!(!b.is_zero(), "div: precondition violated, divisor is zero");
    let num = a.numerator() as i128 * b.denominator() as i128;
    let den = a.denominator() as i128 * b.numerator() as i128;
    from_exact_i128(num, den, Dir::Nearest)
}

/// Always exact: `I2` is symmetric in sign, and `|num| <= 2^62 - 1 <
/// |i64::MIN|` so negation cannot overflow `i64`.
pub fn neg(a: Q) -> Q {
    Q::from_canonical_i128(-(a.numerator() as i128), a.denominator() as i128)
}

/// Always exact.
pub fn abs(a: Q) -> Q {
    Q::from_canonical_i128(
        a.numerator().unsigned_abs() as i128,
        a.denominator() as i128,
    )
}

/// Requires `!a.is_zero()`. Always exact (swaps num/den; see [`div`] for the
/// precondition-enforcement note).
pub fn recip(a: Q) -> Q {
    assert!(!a.is_zero(), "recip: precondition violated, value is zero");
    if a.numerator() > 0 {
        Q::from_canonical_i128(a.denominator() as i128, a.numerator() as i128)
    } else {
        Q::from_canonical_i128(-(a.denominator() as i128), -(a.numerator() as i128))
    }
}

pub fn min(a: Q, b: Q) -> Q {
    if a <= b {
        a
    } else {
        b
    }
}

pub fn max(a: Q, b: Q) -> Q {
    if a >= b {
        a
    } else {
        b
    }
}

/// Requires `lo <= hi`.
pub fn clamp(a: Q, lo: Q, hi: Q) -> Q {
    assert!(lo <= hi, "clamp: precondition violated, lo > hi");
    if a < lo {
        lo
    } else if a > hi {
        hi
    } else {
        a
    }
}

// Idiomatic operator overloads, delegating to the named functions above
// (the spec's canonical API surface). Not part of the spec's MUST table but
// standard Rust ergonomics for a numeric value type.
impl std::ops::Add for Q {
    type Output = Q;
    fn add(self, rhs: Q) -> Q {
        add(self, rhs)
    }
}
impl std::ops::Sub for Q {
    type Output = Q;
    fn sub(self, rhs: Q) -> Q {
        sub(self, rhs)
    }
}
impl std::ops::Mul for Q {
    type Output = Q;
    fn mul(self, rhs: Q) -> Q {
        mul(self, rhs)
    }
}
impl std::ops::Div for Q {
    type Output = Q;
    fn div(self, rhs: Q) -> Q {
        div(self, rhs)
    }
}
impl std::ops::Neg for Q {
    type Output = Q;
    fn neg(self) -> Q {
        neg(self)
    }
}
