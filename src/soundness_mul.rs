//! Issue #28: the containment obligation for `crate::ext::Q::mul`, proven
//! against `crate::denote`'s ghost `XR` model. Same scope discipline as
//! `soundness.rs`: `Number × Number -> Number` (or `-> Sat`) is excluded,
//! governed instead by the already-proven rounding contract (`R1`–`R4`).
//!
//! `mul`'s table is entirely sign-dominance: every non-`Number×Number` cell's
//! answer is (the sign of one operand) times (the sign of the other), with
//! `Nan` appearing only where a `Number` operand could be exactly zero
//! against an infinity (`0 · ∞`). That shared shape is factored into one
//! lemma per "what kind of thing is on each side", not one per cell:
//! `lemma_mul_sound_number_inf` (`Number × Inf`, the only cells that can
//! produce `Nan`), `lemma_mul_sound_sat_inf` and
//! `lemma_mul_sound_inf_inf` (pure sign products, no `Nan` possible: `Sat`
//! and `Inf` are never zero), and `lemma_mul_sound_sat_sat` (`Sat`'s sign
//! product, also never `Nan` since `Sat` is never zero — the one place
//! `mul`'s table has no `Nan` where `add`'s corresponding cell does).

use verus_builtin_macros::verus;

#[allow(unused_imports)]
use verus_builtin::*;
#[allow(unused_imports)]
use vstd::prelude::*;

#[allow(unused_imports)]
use crate::denote::*;
#[allow(unused_imports)]
use crate::ext::*;
#[allow(unused_imports)]
use crate::model::*;
#[allow(unused_imports)]
use crate::types::*;

verus! {

/// **Soundness** for `mul`. See `soundness.rs`'s `add_sound` — same shape,
/// `xr_mul` in place of `xr_add`.
pub open spec fn mul_sound(a: Q, b: Q, r: Q) -> bool {
    forall|u: XR, v: XR|
        xr_wf(u) && xr_wf(v) && denotes(a, u) && denotes(b, v) && xr_mul(u, v).is_some()
            ==> #[trigger] denotes(r, xr_mul(u, v).unwrap())
}

/// **Honesty** for `mul`: `0 · ∞` (either order) forces `Nan`.
pub open spec fn mul_honest(a: Q, b: Q, r: Q) -> bool {
    (exists|u: XR, v: XR|
        xr_wf(u) && xr_wf(v) && denotes(a, u) && denotes(b, v) && xr_mul(u, v).is_none())
        ==> r == Q::Nan
}

/// `xr_mul` is commutative: the `Fin, Fin` case needs multiplication
/// commutativity; every other case is already written symmetrically.
pub proof fn lemma_xr_mul_comm(u: XR, v: XR)
    requires
        xr_wf(u),
        xr_wf(v),
    ensures
        xr_mul(u, v) == xr_mul(v, u),
{
    match (u, v) {
        (XR::Fin(un, ud), XR::Fin(vn, vd)) => {
            assert(un * vn == vn * un) by (nonlinear_arith);
            assert(ud * vd == vd * ud) by (nonlinear_arith);
        },
        _ => {},
    }
}

/// A soundness proof for `(a, b)` lifts to one for `(b, a)`.
pub proof fn lemma_mul_sound_symm(a: Q, b: Q, r: Q)
    requires
        a.wf(),
        b.wf(),
        mul_sound(a, b, r),
    ensures
        mul_sound(b, a, r),
{
    assert forall|u: XR, v: XR|
        xr_wf(u) && xr_wf(v) && denotes(b, u) && denotes(a, v) && xr_mul(u, v).is_some()
        implies #[trigger] denotes(r, xr_mul(u, v).unwrap()) by {
        lemma_xr_mul_comm(u, v);
    }
}

/// **`Number(x) * Inf`.** `Nan` when `x` could be exactly zero (`0 · ∞` is
/// indeterminate); otherwise a signed infinity matching `x`'s sign times
/// `inf_pos`.
pub proof fn lemma_mul_sound_number_inf(x: Rat, inf_pos: bool)
    requires
        x.wf(),
    ensures
        mul_sound(
            Q::Number(x),
            if inf_pos { Q::PosInf } else { Q::NegInf },
            Q::spec_number_times_inf(x, inf_pos),
        ),
{
    let b = if inf_pos { Q::PosInf } else { Q::NegInf };
    assert forall|u: XR, v: XR|
        xr_wf(u) && xr_wf(v) && denotes(Q::Number(x), u) && denotes(b, v) && xr_mul(u, v).is_some()
        implies #[trigger] denotes(Q::spec_number_times_inf(x, inf_pos), xr_mul(u, v).unwrap()) by {
        lemma_denotes_number_unique(x, u);
        if inf_pos {
            lemma_denotes_posinf_unique(v);
        } else {
            lemma_denotes_neginf_unique(v);
        }
        match u {
            XR::Fin(un, ud) => {
                if x.n() == 0 {
                    assert(un == 0) by (nonlinear_arith)
                        requires
                            un * x.d() == x.n() * ud,
                            x.n() == 0,
                            x.d() > 0,
                    ;
                } else if x.n() > 0 {
                    assert(un > 0) by (nonlinear_arith)
                        requires
                            un * x.d() == x.n() * ud,
                            x.n() > 0,
                            x.d() > 0,
                            ud > 0,
                    ;
                } else {
                    assert(un < 0) by (nonlinear_arith)
                        requires
                            un * x.d() == x.n() * ud,
                            x.n() < 0,
                            x.d() > 0,
                            ud > 0,
                    ;
                }
            },
            _ => {},
        }
    }
}

/// **`Sat * Inf`.** Never `Nan`: `Sat` is never zero. Sign product of a
/// fixed-sign `Sat` and a fixed-sign `Inf`.
pub proof fn lemma_mul_sound_sat_inf(sat_pos: bool, inf_pos: bool)
    requires
        true,
    ensures
        mul_sound(
            if sat_pos { Q::PosSat } else { Q::NegSat },
            if inf_pos { Q::PosInf } else { Q::NegInf },
            if sat_pos == inf_pos { Q::PosInf } else { Q::NegInf },
        ),
{
    let a = if sat_pos { Q::PosSat } else { Q::NegSat };
    let b = if inf_pos { Q::PosInf } else { Q::NegInf };
    let r = if sat_pos == inf_pos { Q::PosInf } else { Q::NegInf };
    assert forall|u: XR, v: XR|
        xr_wf(u) && xr_wf(v) && denotes(a, u) && denotes(b, v) && xr_mul(u, v).is_some()
        implies #[trigger] denotes(r, xr_mul(u, v).unwrap()) by {
        if inf_pos {
            lemma_denotes_posinf_unique(v);
        } else {
            lemma_denotes_neginf_unique(v);
        }
        match u {
            XR::Fin(un, ud) => {
                if sat_pos {
                    assert(un > 0) by (nonlinear_arith)
                        requires
                            un > max_mag() * ud,
                            ud > 0,
                            max_mag() >= 0,
                    ;
                } else {
                    assert(un < 0) by (nonlinear_arith)
                        requires
                            un < 0 - max_mag() * ud,
                            ud > 0,
                            max_mag() >= 0,
                    ;
                }
            },
            _ => {},
        }
    }
}

/// **`Inf * Inf`.** Never `Nan`: neither operand is zero. Sign product of
/// two fixed-sign infinities.
pub proof fn lemma_mul_sound_inf_inf(a_pos: bool, b_pos: bool)
    requires
        true,
    ensures
        mul_sound(
            if a_pos { Q::PosInf } else { Q::NegInf },
            if b_pos { Q::PosInf } else { Q::NegInf },
            if a_pos == b_pos { Q::PosInf } else { Q::NegInf },
        ),
{
    let a = if a_pos { Q::PosInf } else { Q::NegInf };
    let b = if b_pos { Q::PosInf } else { Q::NegInf };
    let r = if a_pos == b_pos { Q::PosInf } else { Q::NegInf };
    assert forall|u: XR, v: XR|
        xr_wf(u) && xr_wf(v) && denotes(a, u) && denotes(b, v) && xr_mul(u, v).is_some()
        implies #[trigger] denotes(r, xr_mul(u, v).unwrap()) by {
        if a_pos {
            lemma_denotes_posinf_unique(u);
        } else {
            lemma_denotes_neginf_unique(u);
        }
        if b_pos {
            lemma_denotes_posinf_unique(v);
        } else {
            lemma_denotes_neginf_unique(v);
        }
    }
}

/// **`Sat * Sat`.** Never `Nan`: neither operand is zero. Sign product of
/// two fixed-sign saturations.
pub proof fn lemma_mul_sound_sat_sat(a_pos: bool, b_pos: bool)
    requires
        true,
    ensures
        mul_sound(
            if a_pos { Q::PosSat } else { Q::NegSat },
            if b_pos { Q::PosSat } else { Q::NegSat },
            if a_pos == b_pos { Q::PosSat } else { Q::NegSat },
        ),
{
    let a = if a_pos { Q::PosSat } else { Q::NegSat };
    let b = if b_pos { Q::PosSat } else { Q::NegSat };
    let r = if a_pos == b_pos { Q::PosSat } else { Q::NegSat };
    assert forall|u: XR, v: XR|
        xr_wf(u) && xr_wf(v) && denotes(a, u) && denotes(b, v) && xr_mul(u, v).is_some()
        implies #[trigger] denotes(r, xr_mul(u, v).unwrap()) by {
        match (u, v) {
            (XR::Fin(un, ud), XR::Fin(vn, vd)) => {
                if a_pos && b_pos {
                    assert(un * vn > max_mag() * (ud * vd)) by (nonlinear_arith)
                        requires
                            un > max_mag() * ud,
                            vn > max_mag() * vd,
                            ud > 0,
                            vd > 0,
                            max_mag() >= 0,
                    ;
                } else if !a_pos && !b_pos {
                    assert(un * vn > max_mag() * (ud * vd)) by (nonlinear_arith)
                        requires
                            un < 0 - max_mag() * ud,
                            vn < 0 - max_mag() * vd,
                            ud > 0,
                            vd > 0,
                            max_mag() >= 0,
                    ;
                } else if a_pos && !b_pos {
                    assert(un * vn < 0 - max_mag() * (ud * vd)) by (nonlinear_arith)
                        requires
                            un > max_mag() * ud,
                            vn < 0 - max_mag() * vd,
                            ud > 0,
                            vd > 0,
                            max_mag() >= 0,
                    ;
                } else {
                    assert(un * vn < 0 - max_mag() * (ud * vd)) by (nonlinear_arith)
                        requires
                            un < 0 - max_mag() * ud,
                            vn > max_mag() * vd,
                            ud > 0,
                            vd > 0,
                            max_mag() >= 0,
                    ;
                }
            },
            _ => {},
        }
    }
}

/// **`Q::mul` is sound**, restricted to the special-value propagation
/// cells.
pub proof fn theorem_mul_sound(a: Q, b: Q)
    requires
        a.wf(),
        b.wf(),
        !(a.spec_is_number() && b.spec_is_number()),
    ensures
        mul_sound(a, b, Q::spec_mul(a, b)),
{
    match (a, b) {
        (Q::Nan, _) | (_, Q::Nan) => {},
        (Q::Number(_), Q::Number(_)) => {
            assert(false);
        },
        (Q::Number(x), Q::PosInf) => {
            lemma_mul_sound_number_inf(x, true);
        },
        (Q::Number(x), Q::NegInf) => {
            lemma_mul_sound_number_inf(x, false);
        },
        (Q::PosInf, Q::Number(y)) => {
            lemma_mul_sound_number_inf(y, true);
            lemma_mul_sound_symm(Q::Number(y), Q::PosInf, Q::spec_number_times_inf(y, true));
        },
        (Q::NegInf, Q::Number(y)) => {
            lemma_mul_sound_number_inf(y, false);
            lemma_mul_sound_symm(Q::Number(y), Q::NegInf, Q::spec_number_times_inf(y, false));
        },
        (Q::Number(x), Q::PosSat) => {
            lemma_mul_sound_number_sat(x, true);
        },
        (Q::Number(x), Q::NegSat) => {
            lemma_mul_sound_number_sat(x, false);
        },
        (Q::PosSat, Q::Number(y)) => {
            lemma_mul_sound_number_sat(y, true);
            lemma_mul_sound_symm(Q::Number(y), Q::PosSat, Q::spec_number_times_sat(y, true));
        },
        (Q::NegSat, Q::Number(y)) => {
            lemma_mul_sound_number_sat(y, false);
            lemma_mul_sound_symm(Q::Number(y), Q::NegSat, Q::spec_number_times_sat(y, false));
        },
        (Q::PosSat, Q::PosSat) => {
            lemma_mul_sound_sat_sat(true, true);
        },
        (Q::PosSat, Q::NegSat) => {
            lemma_mul_sound_sat_sat(true, false);
        },
        (Q::NegSat, Q::PosSat) => {
            lemma_mul_sound_sat_sat(false, true);
        },
        (Q::NegSat, Q::NegSat) => {
            lemma_mul_sound_sat_sat(false, false);
        },
        (Q::PosSat, Q::PosInf) => {
            lemma_mul_sound_sat_inf(true, true);
        },
        (Q::PosSat, Q::NegInf) => {
            lemma_mul_sound_sat_inf(true, false);
        },
        (Q::NegSat, Q::PosInf) => {
            lemma_mul_sound_sat_inf(false, true);
        },
        (Q::NegSat, Q::NegInf) => {
            lemma_mul_sound_sat_inf(false, false);
        },
        (Q::PosInf, Q::PosSat) => {
            lemma_mul_sound_sat_inf(true, true);
            lemma_mul_sound_symm(Q::PosSat, Q::PosInf, Q::PosInf);
        },
        (Q::PosInf, Q::NegSat) => {
            lemma_mul_sound_sat_inf(false, true);
            lemma_mul_sound_symm(Q::NegSat, Q::PosInf, Q::NegInf);
        },
        (Q::NegInf, Q::PosSat) => {
            lemma_mul_sound_sat_inf(true, false);
            lemma_mul_sound_symm(Q::PosSat, Q::NegInf, Q::NegInf);
        },
        (Q::NegInf, Q::NegSat) => {
            lemma_mul_sound_sat_inf(false, false);
            lemma_mul_sound_symm(Q::NegSat, Q::NegInf, Q::PosInf);
        },
        (Q::PosInf, Q::PosInf) => {
            lemma_mul_sound_inf_inf(true, true);
        },
        (Q::PosInf, Q::NegInf) => {
            lemma_mul_sound_inf_inf(true, false);
        },
        (Q::NegInf, Q::PosInf) => {
            lemma_mul_sound_inf_inf(false, true);
        },
        (Q::NegInf, Q::NegInf) => {
            lemma_mul_sound_inf_inf(false, false);
        },
    }
}

/// **`Number(x) * Sat`.** Never `Nan` when `x` could be zero — that's exactly
/// `Number(0)`; both sides then denote `0`, so the true product is `0`, and
/// `spec_number_times_sat` correctly returns `Number(0)` there. `Nan` instead
/// appears where `0 < |x| < 1`, an image that reaches back inside the
/// budget.
pub proof fn lemma_mul_sound_number_sat(x: Rat, sat_pos: bool)
    requires
        x.wf(),
    ensures
        mul_sound(
            Q::Number(x),
            if sat_pos { Q::PosSat } else { Q::NegSat },
            Q::spec_number_times_sat(x, sat_pos),
        ),
{
    let b = if sat_pos { Q::PosSat } else { Q::NegSat };
    assert forall|u: XR, v: XR|
        xr_wf(u) && xr_wf(v) && denotes(Q::Number(x), u) && denotes(b, v) && xr_mul(u, v).is_some()
        implies #[trigger] denotes(Q::spec_number_times_sat(x, sat_pos), xr_mul(u, v).unwrap()) by {
        lemma_denotes_number_unique(x, u);
        match (u, v) {
            (XR::Fin(un, ud), XR::Fin(vn, vd)) => {
                if x.n() == 0 {
                    assert(un == 0) by (nonlinear_arith)
                        requires
                            un * x.d() == x.n() * ud,
                            x.n() == 0,
                            x.d() > 0,
                    ;
                    assert(un * vn == 0) by (nonlinear_arith)
                        requires
                            un == 0,
                    ;
                    Rat::lemma_from_raw_spec_components(0, 1);
                    assert((un * vn) * 1 == 0 * (ud * vd)) by (nonlinear_arith)
                        requires
                            un * vn == 0,
                    ;
                } else {
                    let at_least_one = x.n() >= x.d() || x.n() <= 0 - x.d();
                    if at_least_one {
                        if sat_pos {
                            if (x.n() > 0) {
                                assert(un * vn > max_mag() * (ud * vd)) by (nonlinear_arith)
                                    requires
                                        un * x.d() == x.n() * ud,
                                        x.n() >= x.d(),
                                        x.d() > 0,
                                        ud > 0,
                                        vn > max_mag() * vd,
                                        vd > 0,
                                        max_mag() >= 0,
                                ;
                            } else {
                                assert(un * vn < 0 - max_mag() * (ud * vd)) by (nonlinear_arith)
                                    requires
                                        un * x.d() == x.n() * ud,
                                        x.n() <= 0 - x.d(),
                                        x.d() > 0,
                                        ud > 0,
                                        vn > max_mag() * vd,
                                        vd > 0,
                                        max_mag() >= 0,
                                ;
                            }
                        } else {
                            if (x.n() > 0) {
                                assert(un * vn < 0 - max_mag() * (ud * vd)) by (nonlinear_arith)
                                    requires
                                        un * x.d() == x.n() * ud,
                                        x.n() >= x.d(),
                                        x.d() > 0,
                                        ud > 0,
                                        vn < 0 - max_mag() * vd,
                                        vd > 0,
                                        max_mag() >= 0,
                                ;
                            } else {
                                assert(un * vn > max_mag() * (ud * vd)) by (nonlinear_arith)
                                    requires
                                        un * x.d() == x.n() * ud,
                                        x.n() <= 0 - x.d(),
                                        x.d() > 0,
                                        ud > 0,
                                        vn < 0 - max_mag() * vd,
                                        vd > 0,
                                        max_mag() >= 0,
                                ;
                            }
                        }
                    }
                }
            },
            _ => {},
        }
    }
}

/// `Sat`'s `Fin` is never the zero value: `n > max_mag() * d` (or the mirror)
/// with `d > 0`, `max_mag() >= 0` already forces `n`'s sign.
pub proof fn lemma_sat_never_zero(pos: bool, v: XR)
    requires
        xr_wf(v),
        denotes(if pos { Q::PosSat } else { Q::NegSat }, v),
    ensures
        match v {
            XR::Fin(n, _d) => n != 0,
            _ => true,
        },
{
    match v {
        XR::Fin(n, d) => {
            if pos {
                assert(n > 0) by (nonlinear_arith)
                    requires
                        n > max_mag() * d,
                        d > 0,
                        max_mag() >= 0,
                ;
            } else {
                assert(n < 0) by (nonlinear_arith)
                    requires
                        n < 0 - max_mag() * d,
                        d > 0,
                        max_mag() >= 0,
                ;
            }
        },
        _ => {},
    }
}

/// Whenever `a` is not `Number(0)`-shaped and not `Nan`, `a`'s denotation
/// contains no zero: `Sat` and `Inf` are never zero, and a nonzero `Number`
/// denotes only that nonzero value. Packaged once so every `mul_honest`
/// case that isn't `Number × Inf` can discharge "no witness is zero" without
/// its own nonlinear step.
proof fn lemma_denotes_never_zero_fin(a: Q, u: XR)
    requires
        a.wf(),
        !a.spec_is_nan(),
        !(a.spec_is_number() && a.spec_is_zero()),
        xr_wf(u),
        denotes(a, u),
    ensures
        match u {
            XR::Fin(n, _d) => n != 0,
            _ => true,
        },
{
    match a {
        Q::Number(x) => {
            lemma_denotes_number_unique(x, u);
            match u {
                XR::Fin(un, ud) => {
                    assert(un != 0) by (nonlinear_arith)
                        requires
                            un * x.d() == x.n() * ud,
                            x.n() != 0,
                            x.d() > 0,
                            ud > 0,
                    ;
                },
                _ => {},
            }
        },
        Q::PosSat => {
            lemma_sat_never_zero(true, u);
        },
        Q::NegSat => {
            lemma_sat_never_zero(false, u);
        },
        Q::PosInf | Q::NegInf | Q::Nan => {},
    }
}

/// **`Q::mul` is honest.** `mul`'s only indeterminate, `0 · ∞`, can only be
/// witnessed when one operand is `Number(0)` and the other an infinity — and
/// those are exactly `spec_number_times_inf`'s `Nan` sub-branch.
pub proof fn theorem_mul_honest(a: Q, b: Q)
    requires
        a.wf(),
        b.wf(),
    ensures
        mul_honest(a, b, Q::spec_mul(a, b)),
{
    if exists|u: XR, v: XR|
        xr_wf(u) && xr_wf(v) && denotes(a, u) && denotes(b, v) && xr_mul(u, v).is_none() {
        let (u, v): (XR, XR) = choose|u: XR, v: XR|
            xr_wf(u) && xr_wf(v) && denotes(a, u) && denotes(b, v) && xr_mul(u, v).is_none();
        match (a, b) {
            (Q::Number(x), Q::PosInf) | (Q::Number(x), Q::NegInf) => {
                lemma_denotes_number_unique(x, u);
                match u {
                    XR::Fin(un, ud) => {
                        assert(un == 0);
                        assert(x.n() == 0) by (nonlinear_arith)
                            requires
                                un * x.d() == x.n() * ud,
                                un == 0,
                                x.d() > 0,
                                ud > 0,
                        ;
                    },
                    _ => { assert(false); },
                }
                assert(Q::spec_mul(a, b) == Q::Nan);
            },
            (Q::PosInf, Q::Number(y)) | (Q::NegInf, Q::Number(y)) => {
                lemma_denotes_number_unique(y, v);
                match v {
                    XR::Fin(vn, vd) => {
                        assert(vn == 0);
                        assert(y.n() == 0) by (nonlinear_arith)
                            requires
                                vn * y.d() == y.n() * vd,
                                vn == 0,
                                y.d() > 0,
                                vd > 0,
                        ;
                    },
                    _ => { assert(false); },
                }
                assert(Q::spec_mul(a, b) == Q::Nan);
            },
            (Q::Nan, _) | (_, Q::Nan) => {
                assert(Q::spec_mul(a, b) == Q::Nan);
            },
            _ => {
                // Every other pair: `xr_mul(u, v)` cannot be `None` at all.
                // `Fin, Fin` and `Infinity, Infinity` are total; a `Fin`
                // against an `Infinity` needs a zero `Fin`, and neither
                // `Sat`'s nor a non-`Number`-paired `Number`'s denotation
                // (excluded above) can be zero here.
                if a.spec_is_infinite() {
                    lemma_denotes_never_zero_fin(b, v);
                } else if b.spec_is_infinite() {
                    lemma_denotes_never_zero_fin(a, u);
                }
                match (u, v) {
                    (XR::Fin(_, _), XR::Fin(_, _)) => {
                        assert(xr_mul(u, v).is_some());
                    },
                    (XR::PosInfinity, XR::Fin(vn, _)) | (XR::NegInfinity, XR::Fin(vn, _)) => {
                        assert(vn != 0);
                        assert(xr_mul(u, v).is_some());
                    },
                    (XR::Fin(un, _), XR::PosInfinity) | (XR::Fin(un, _), XR::NegInfinity) => {
                        assert(un != 0);
                        assert(xr_mul(u, v).is_some());
                    },
                    (XR::PosInfinity, XR::PosInfinity) | (XR::PosInfinity, XR::NegInfinity)
                    | (XR::NegInfinity, XR::PosInfinity) | (XR::NegInfinity, XR::NegInfinity) => {
                        assert(xr_mul(u, v).is_some());
                    },
                }
                // Contradicts the `xr_mul(u, v).is_none()` from `choose`.
                assert(false);
            },
        }
    }
}

} // verus!
