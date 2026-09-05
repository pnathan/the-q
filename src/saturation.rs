//! The scoping of the rounding contract at the magnitude ceiling, as one lemma.
//!
//! R3 is stated under `!saturated(n, d)`: results above the ceiling saturate,
//! and `checked_*` reports them as `None`. The natural justification for that
//! scoping — that nothing representable is close enough up there, so the bound
//! is unachievable — is false. `lemma_saturation_is_a_choice` (no intra-doc
//! link: items inside `verus!` are not resolvable targets) exhibits a value
//! outside the ceiling that a well-formed `Rat` satisfies R3 for, so the strong
//! claim contradicts a machine-checked theorem rather than a comment.
//!
//! The module boundary is organisational, not load-bearing: the lemma verifies
//! cleanly from `model` under the pinned toolchain (issue #15), so it can be
//! folded back in.
//!
//! Excluding the region above the ceiling keeps R3 on one side of a clean
//! boundary and keeps `checked_*` honest. It is a choice, not a necessity.

use verus_builtin_macros::verus;

#[allow(unused_imports)]
use verus_builtin::*;
#[allow(unused_imports)]
use vstd::prelude::*;

#[allow(unused_imports)]
use crate::model::*;
#[allow(unused_imports)]
use crate::types::{MAX_MAG, Rat};

verus! {

/// Saturation is a scoping choice, not a necessity: `MAX_MAG + 1/2` is within
/// R3 of `MAX_MAG/1` (error `1/2`, allowed nearly `2`).
pub proof fn lemma_saturation_is_a_choice()
    ensures
        !magnitude_fits(2 * max_mag() + 1, 2),
        Rat::from_raw_spec(MAX_MAG, 1).wf(),
        within_error_bound(Rat::from_raw_spec(MAX_MAG, 1), 2 * max_mag() + 1, 2),
{
    let n = 2 * max_mag() + 1;
    let r = Rat::from_raw_spec(MAX_MAG, 1);
    Rat::lemma_from_raw_spec_components(MAX_MAG, 1);
    lemma_max_mag_pow2();
    // Resolve the closed abstract components before reasoning about them
    // arithmetically.
    assert(r.n() == max_mag());
    assert(r.d() == 1);
    // I1: gcd(MAX_MAG, 1) unfolds to gcd(1, 0) == 1, so it needs two steps of
    // fuel — the definition recurses on the second argument.
    assert(gcd_int(r.n(), r.d()) == 1) by {
        reveal_with_fuel(gcd_nat, 3);
    }
    // Outside the ceiling: |n| == 2·MAX_MAG + 1 > MAX_MAG · 2.
    assert(!magnitude_fits(n, 2));
    // The error is one half, written division-free as |r.num·d − n·r.den| == 1.
    assert(r.n() * 2 - n * r.d() == -1);
    assert(abs_int(r.n() * 2 - n * r.d()) == 1);
    // R3 allows `r.den · max(d, |n|)` == 2·MAX_MAG + 1 == 2^63 − 1, against the
    // 2^61 the error costs.
    assert(max_int(2, abs_int(n)) == n);
    // `n == 2·max_mag() + 1 == 2·2^62 − 1`, and `2^61 < 2^62`, so the bound has
    // room to spare. Stated via monotonicity rather than by unfolding `pow2` up
    // to 63 — the high fuel that needs is enough to destabilise other proofs in
    // this module.
    lemma_pow2_pos(62nat);
    lemma_pow2_mono(61nat, 62nat);
}

} // verus!
