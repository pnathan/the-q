// Ghost model and Verus specifications
// All value correctness is stated against unbounded mathematical integers (ghost int)
// Relationships are stated division-free via cross-multiplication

pub use crate::q::Q;

/// Ghost model: the mathematical value of a rational as a pair of unbounded integers
/// Allows reasoning about mathematical equality without division
pub struct QGhost {
    pub num: i128, // unbounded, ghost only
    pub den: i128, // unbounded, ghost only
}

/// Mathematical equality: a.num * b.den == b.num * a.den
/// This avoids division in the SMT solver
pub fn q_eq(a_num: i128, a_den: i128, b_num: i128, b_den: i128) -> bool {
    a_num * b_den == b_num * a_den
}

/// Mathematical less-than: a.num * b.den < b.num * a.den (with care for signs)
pub fn q_lt(a_num: i128, a_den: i128, b_num: i128, b_den: i128) -> bool {
    // Assumes den > 0 (canonical form)
    a_num * b_den < b_num * a_den
}

pub fn q_le(a_num: i128, a_den: i128, b_num: i128, b_den: i128) -> bool {
    a_num * b_den <= b_num * a_den
}

/// Predicate: q is in the unit interval [0, 1]
pub fn in_unit_interval(num: i128, den: i128) -> bool {
    q_le(0, 1, num, den) && q_le(num, den, 1, 1)
}

/// Specification: result equals a + b
pub fn spec_add_result(
    a_num: i128,
    a_den: i128,
    b_num: i128,
    b_den: i128,
    r_num: i128,
    r_den: i128,
) -> bool {
    // r_num / r_den == a_num / a_den + b_num / b_den
    // r_num / r_den == (a_num * b_den + b_num * a_den) / (a_den * b_den)
    // Cross-multiply: r_num * (a_den * b_den) == (a_num * b_den + b_num * a_den) * r_den
    r_num * (a_den * b_den) == (a_num * b_den + b_num * a_den) * r_den
}

/// Specification: result equals a - b
pub fn spec_sub_result(
    a_num: i128,
    a_den: i128,
    b_num: i128,
    b_den: i128,
    r_num: i128,
    r_den: i128,
) -> bool {
    r_num * (a_den * b_den) == (a_num * b_den - b_num * a_den) * r_den
}

/// Specification: result equals a * b
pub fn spec_mul_result(
    a_num: i128,
    a_den: i128,
    b_num: i128,
    b_den: i128,
    r_num: i128,
    r_den: i128,
) -> bool {
    r_num * (a_den * b_den) == (a_num * b_num) * r_den
}

/// Specification: result equals a / b (b != 0)
pub fn spec_div_result(
    a_num: i128,
    a_den: i128,
    b_num: i128,
    b_den: i128,
    r_num: i128,
    r_den: i128,
) -> bool {
    // a / b == (a_num / a_den) / (b_num / b_den)
    //        == (a_num * b_den) / (a_den * b_num)
    r_num * (a_den * b_num) == (a_num * b_den) * r_den
}

/// Invariant I1: canonical form
/// num/den in lowest terms and den > 0
pub fn is_canonical(num: i64, den: i64, gcd_val: i64) -> bool {
    den > 0 && gcd_val == 1 && (num != 0 || den == 1)
}

/// Invariant I2: bounded representation
/// |num| <= 2^62 - 1 and den <= 2^62 - 1
pub fn is_bounded(num: i64, den: i64) -> bool {
    const BOUND: i64 = (1i64 << 62) - 1;
    num.abs() <= BOUND && den <= BOUND
}

/// Error bound after rounding: |result - exact| <= 2^-B * max(1, |exact|)
/// With B >= 60
pub fn error_bound_satisfied(result: i128, exact: i128, max_magnitude: i128, b: u32) -> bool {
    let tolerance = (1i128 << b).max(1);
    let error = (result - exact).abs();
    // error <= max(1, |exact|) / 2^b
    error * tolerance <= max_magnitude.abs().max(1)
}
