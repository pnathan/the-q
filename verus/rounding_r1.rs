// V4 / R1: identity on representables. If the exact, GCD-reduced result of
// an op already satisfies the I2 budget, `from_exact_i128` returns it
// *unchanged* -- no rounding ever touches it. This is the fact that makes
// "any computation whose exact values all fit the budget is end-to-end
// exact" true (spec §3).
//
// Standalone Verus proof file mirroring `rounding::from_exact_i128` in
// src/rounding.rs. Checked directly via `verus verus/rounding_r1.rs`; see
// verus/smoke_test.rs's header comment for why these live outside the
// cargo package. R2 (directedness), R3 (the 2^-60 error bound), and R4
// (monotonicity) -- the harder parts of V4, covering `round_to_budget`
// itself -- are not attempted in this pass; see TRUSTED.md.
//
// Authored and iterated on entirely via CI feedback -- no local Verus
// available (see TRUSTED.md).

use vstd::prelude::*;

verus! {

pub open spec fn max_mag() -> int {
    0x3FFF_FFFF_FFFF_FFFF
}

pub open spec fn fits_budget(num: int, den: int) -> bool {
    -max_mag() <= num && num <= max_mag() && 1 <= den && den <= max_mag()
}

fn fits_in_budget(num: i128, den: i128) -> (result: bool)
    ensures
        result == fits_budget(num as int, den as int),
{
    let max_mag: i128 = 0x3FFF_FFFF_FFFF_FFFF;
    (-max_mag <= num && num <= max_mag) && (1 <= den && den <= max_mag)
}

/// Stand-in for `round_to_budget` -- deliberately unmodeled here (R2-R4,
/// the directed-rounding contract it must satisfy, are out of scope for
/// this file; see TRUSTED.md). Its only role in this proof is to occupy
/// the `else` branch so `from_exact_pair` structurally mirrors the real
/// `from_exact_i128`.
#[verifier::external_body]
fn round_to_budget_stub(num: i128, den: i128) -> (i128, i128) {
    unimplemented!()
}

/// Mirrors `from_exact_i128`: canonicalize is modeled as already having
/// happened (V1/V3 cover that separately, in gcd.rs and
/// value_correctness.rs) -- `num`/`den` here are the already-canonical
/// exact pair. R1 itself: when that pair is already in budget, the result
/// is the pair unchanged.
fn from_exact_pair(num: i128, den: i128) -> (result: (i128, i128))
    requires
        den > 0,
    ensures
        fits_budget(num as int, den as int) ==> result == (num, den),
{
    if fits_in_budget(num, den) {
        (num, den)
    } else {
        round_to_budget_stub(num, den)
    }
}

fn main() {}

} // verus!
