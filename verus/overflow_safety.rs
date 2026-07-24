// V2: no panic, no overflow -- every i128 intermediate in add/sub/mul is
// provably in range given I2-bounded (i64) inputs.
//
// Standalone Verus proof file mirroring the formulas in `src/ops.rs`
// (add/sub/mul) in the shipped crate. Checked directly via
// `verus verus/overflow_safety.rs`; see verus/smoke_test.rs's header
// comment for why these live outside the cargo package, and TRUSTED.md for
// the full accounting.
//
// Authored and iterated on entirely via CI feedback -- no local Verus
// available (see TRUSTED.md).

use vstd::prelude::*;

verus! {

/// `2^62 - 1`, the I2 bound on `|num|` and `den`.
pub open spec fn max_mag() -> int {
    0x3FFF_FFFF_FFFF_FFFF
}

pub open spec fn in_budget_num(n: int) -> bool {
    -max_mag() <= n && n <= max_mag()
}

pub open spec fn in_budget_den(d: int) -> bool {
    1 <= d && d <= max_mag()
}

/// Both factors of a mul's numerator/denominator formulas are I2-bounded,
/// so their product's magnitude is at most `max_mag()^2 < 2^124`, far under
/// `i128`'s `2^127 - 1` ceiling.
fn mul_intermediate(n1: i64, d1: i64, n2: i64, d2: i64) -> (result: (i128, i128))
    requires
        in_budget_num(n1 as int),
        in_budget_den(d1 as int),
        in_budget_num(n2 as int),
        in_budget_den(d2 as int),
    ensures
        result.0 == n1 as i128 * n2 as i128,
        result.1 == d1 as i128 * d2 as i128,
{
    assert(n1 as i128 * n2 as i128 <= max_mag() * max_mag()) by (nonlinear_arith)
        requires
            in_budget_num(n1 as int),
            in_budget_num(n2 as int),
    {}
    assert(n1 as i128 * n2 as i128 >= -(max_mag() * max_mag())) by (nonlinear_arith)
        requires
            in_budget_num(n1 as int),
            in_budget_num(n2 as int),
    {}
    assert(d1 as i128 * d2 as i128 <= max_mag() * max_mag()) by (nonlinear_arith)
        requires
            in_budget_den(d1 as int),
            in_budget_den(d2 as int),
    {}
    assert(d1 as i128 * d2 as i128 >= 1) by (nonlinear_arith)
        requires
            in_budget_den(d1 as int),
            in_budget_den(d2 as int),
    {}
    let num = n1 as i128 * n2 as i128;
    let den = d1 as i128 * d2 as i128;
    (num, den)
}

/// The add/sub numerator formula `n1*d2 +/- n2*d1`: each product is
/// I2-bounded (`<= max_mag()^2`), so the sum/difference of two such terms
/// is at most `2 * max_mag()^2 < 2^125`, still far under `i128`'s ceiling.
/// The denominator formula `d1*d2` is the same as `mul_intermediate`'s.
fn add_intermediate(n1: i64, d1: i64, n2: i64, d2: i64) -> (result: (i128, i128))
    requires
        in_budget_num(n1 as int),
        in_budget_den(d1 as int),
        in_budget_num(n2 as int),
        in_budget_den(d2 as int),
    ensures
        result.0 == n1 as i128 * d2 as i128 + n2 as i128 * d1 as i128,
        result.1 == d1 as i128 * d2 as i128,
{
    assert(n1 as i128 * d2 as i128 <= max_mag() * max_mag() && n1 as i128 * d2 as i128
        >= -(max_mag() * max_mag())) by (nonlinear_arith)
        requires
            in_budget_num(n1 as int),
            in_budget_den(d2 as int),
    {}
    assert(n2 as i128 * d1 as i128 <= max_mag() * max_mag() && n2 as i128 * d1 as i128
        >= -(max_mag() * max_mag())) by (nonlinear_arith)
        requires
            in_budget_num(n2 as int),
            in_budget_den(d1 as int),
    {}
    assert(d1 as i128 * d2 as i128 <= max_mag() * max_mag() && d1 as i128 * d2 as i128 >= 1)
        by (nonlinear_arith)
        requires
            in_budget_den(d1 as int),
            in_budget_den(d2 as int),
    {}
    let num = n1 as i128 * d2 as i128 + n2 as i128 * d1 as i128;
    let den = d1 as i128 * d2 as i128;
    (num, den)
}

fn sub_intermediate(n1: i64, d1: i64, n2: i64, d2: i64) -> (result: (i128, i128))
    requires
        in_budget_num(n1 as int),
        in_budget_den(d1 as int),
        in_budget_num(n2 as int),
        in_budget_den(d2 as int),
    ensures
        result.0 == n1 as i128 * d2 as i128 - n2 as i128 * d1 as i128,
        result.1 == d1 as i128 * d2 as i128,
{
    assert(n1 as i128 * d2 as i128 <= max_mag() * max_mag() && n1 as i128 * d2 as i128
        >= -(max_mag() * max_mag())) by (nonlinear_arith)
        requires
            in_budget_num(n1 as int),
            in_budget_den(d2 as int),
    {}
    assert(n2 as i128 * d1 as i128 <= max_mag() * max_mag() && n2 as i128 * d1 as i128
        >= -(max_mag() * max_mag())) by (nonlinear_arith)
        requires
            in_budget_num(n2 as int),
            in_budget_den(d1 as int),
    {}
    assert(d1 as i128 * d2 as i128 <= max_mag() * max_mag() && d1 as i128 * d2 as i128 >= 1)
        by (nonlinear_arith)
        requires
            in_budget_den(d1 as int),
            in_budget_den(d2 as int),
    {}
    let num = n1 as i128 * d2 as i128 - n2 as i128 * d1 as i128;
    let den = d1 as i128 * d2 as i128;
    (num, den)
}

/// The `div` formula reuses the exact same shape as `mul` (`a.num*b.den`,
/// `a.den*b.num`) with `b.num` in place of a second denominator -- bounded
/// identically since `b.num` is also I2-bounded.
fn div_intermediate(n1: i64, d1: i64, n2: i64, d2: i64) -> (result: (i128, i128))
    requires
        in_budget_num(n1 as int),
        in_budget_den(d1 as int),
        in_budget_num(n2 as int),
        in_budget_den(d2 as int),
    ensures
        result.0 == n1 as i128 * d2 as i128,
        result.1 == d1 as i128 * n2 as i128,
{
    assert(n1 as i128 * d2 as i128 <= max_mag() * max_mag() && n1 as i128 * d2 as i128
        >= -(max_mag() * max_mag())) by (nonlinear_arith)
        requires
            in_budget_num(n1 as int),
            in_budget_den(d2 as int),
    {}
    assert(d1 as i128 * n2 as i128 <= max_mag() * max_mag() && d1 as i128 * n2 as i128
        >= -(max_mag() * max_mag())) by (nonlinear_arith)
        requires
            in_budget_den(d1 as int),
            in_budget_num(n2 as int),
    {}
    let num = n1 as i128 * d2 as i128;
    let den = d1 as i128 * n2 as i128;
    (num, den)
}

/// The `cmp` formula (`a.num*b.den` vs `b.num*a.den`) is bounded the same
/// way as a single side of `add`'s numerator.
fn cmp_intermediate(n1: i64, d1: i64, n2: i64, d2: i64) -> (result: (i128, i128))
    requires
        in_budget_num(n1 as int),
        in_budget_den(d1 as int),
        in_budget_num(n2 as int),
        in_budget_den(d2 as int),
    ensures
        result.0 == n1 as i128 * d2 as i128,
        result.1 == n2 as i128 * d1 as i128,
{
    assert(n1 as i128 * d2 as i128 <= max_mag() * max_mag() && n1 as i128 * d2 as i128
        >= -(max_mag() * max_mag())) by (nonlinear_arith)
        requires
            in_budget_num(n1 as int),
            in_budget_den(d2 as int),
    {}
    assert(n2 as i128 * d1 as i128 <= max_mag() * max_mag() && n2 as i128 * d1 as i128
        >= -(max_mag() * max_mag())) by (nonlinear_arith)
        requires
            in_budget_num(n2 as int),
            in_budget_den(d1 as int),
    {}
    let lhs = n1 as i128 * d2 as i128;
    let rhs = n2 as i128 * d1 as i128;
    (lhs, rhs)
}

fn main() {}

} // verus!
