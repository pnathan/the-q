//! Ghost model: the mathematical objects every executable function is
//! specified against. Everything here is spec-level (erased at runtime).
//!
//! Discipline (mirrors the parent Lean formalization): all value statements
//! are division-free, phrased by cross-multiplication over unbounded `int`.

use vstd::prelude::*;

verus! {

/// Magnitude budget for numerator and denominator: `2^62 - 1` (invariant I2).
///
/// Why `2^62` and not `2^63`: every intermediate is computed exactly in
/// `i128`; the worst case is the add/sub numerator `n1*d2 + n2*d1` with all
/// four factors at the budget, which is `< 2^125` under the `2^62` budget but
/// would reach `2^127` (overflowing `i128::MAX = 2^127 - 1`) under `2^63`.
pub const MAX_MAG: i64 = 0x3FFF_FFFF_FFFF_FFFF;

/// `MAX_MAG` as a spec-level int.
pub open spec fn max_mag() -> int {
    0x3FFF_FFFF_FFFF_FFFF
}

/// Spec-level absolute value over int.
pub open spec fn abs_i(x: int) -> int {
    if x < 0 { -x } else { x }
}

/// Euclidean greatest common divisor over nat. `gcd(0, 0) == 0`.
pub open spec fn gcd(a: nat, b: nat) -> nat
    decreases b,
{
    if b == 0 { a } else { gcd(b, a % b) }
}

/// `d` divides `n` (over nat).
pub open spec fn divides(d: nat, n: nat) -> bool {
    exists|k: nat| n == #[trigger] (d * k)
}

} // verus!
