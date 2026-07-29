//! One lemma, isolated on purpose.
//!
//! The rounding contract is scoped below the magnitude ceiling: R3 is stated
//! under `!saturated(n, d)`, results above it saturate, and `checked_*` reports
//! them as `None`. The tempting justification for that — *nothing representable
//! is close enough up there, so the bound is unachievable* — is *false*, and
//! attractive enough that it was written into this crate three separate times by
//! two different authors, and corrected twice before it stopped coming back.
//!
//! Prose rots. A proof obligation does not. `lemma_saturation_is_a_choice`
//! (no intra-doc link: items inside `verus!` are not resolvable targets)
//! exhibits a value outside the ceiling that a well-formed `Q` satisfies R3 for,
//! so the strong claim now contradicts a machine-checked theorem rather than a
//! comment somebody has to remember.
//!
//! It lives in its own module for no better reason than that it did not belong
//! anywhere in particular. An earlier version of this note claimed the
//! separation was forced — that the lemma's SMT cost tipped marginal proofs in
//! `model` and `laws`. That was wrong: re-running the experiment under the
//! pinned toolchain verifies cleanly with the lemma in `model` (see the closed
//! issue #15), so nothing here is load-bearing and it can be folded back in if
//! anyone prefers.
//!
//! None of this argues for widening the contract. Excluding the region keeps R3
//! on one clean side of a boundary and keeps `checked_*` honest. It is simply
//! not forced, and the documentation should not say it is.

use verus_builtin_macros::verus;

#[allow(unused_imports)]
use verus_builtin::*;
#[allow(unused_imports)]
use vstd::prelude::*;

#[allow(unused_imports)]
use crate::model::*;
#[allow(unused_imports)]
use crate::types::{MAX_MAG, Q};

verus! {

/// Saturation is a **scoping choice, not a necessity**: there are values above
/// the magnitude ceiling that a well-formed `Q` does satisfy R3 for.
///
/// This exists because the opposite claim — that nothing representable is close
/// enough, so the bound is unachievable up there — is false, and is attractive
/// enough that it was written into this crate's documentation three separate
/// times by two different authors, and corrected twice before it stopped coming
/// back. A sentence can rot; a proof obligation cannot. If anyone restates the
/// strong version, this lemma is the thing that contradicts them.
///
/// The witness is `n/d = MAX_MAG + 1/2` against `r = MAX_MAG/1`: the error is
/// exactly `1/2`, and R3 at this magnitude allows nearly `2`.
///
/// None of this says the crate should widen the contract. Excluding the region
/// keeps R3 on one clean side of a boundary and keeps `checked_*` honest. It
/// just is not forced, and the docs should not claim it is.
pub proof fn lemma_saturation_is_a_choice()
    ensures
        !magnitude_fits(2 * max_mag() + 1, 2),
        (Q { num: MAX_MAG, den: 1 }).wf(),
        within_error_bound(Q { num: MAX_MAG, den: 1 }, 2 * max_mag() + 1, 2),
{
    let n = 2 * max_mag() + 1;
    let r = Q { num: MAX_MAG, den: 1 };
    lemma_max_mag_pow2();
    // Resolve the field accesses on the struct literal before anything reasons
    // about them arithmetically.
    assert(r.n() == max_mag());
    assert(r.d() == 1);
    // I1: gcd(MAX_MAG, 1) unfolds to gcd(1, 0) == 1, so it needs two steps of
    // fuel — the definition recurses on the second argument.
    assert(gcd_int(r.num as int, r.den as int) == 1) by {
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
