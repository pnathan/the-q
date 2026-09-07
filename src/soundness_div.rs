//! Issue #28: the containment obligation for [`crate::ext::Q::div`], proven
//! against [`crate::denote`]'s ghost `XR` model. Same scope discipline as
//! `soundness.rs`/`soundness_mul.rs`: `Number × Number` is excluded
//! (`R1`–`R4`'s job), including its zero-divisor sub-case.
//!
//! `div` needs the least new casework of the three: five of its six
//! "produces `Nan`" cells (`Number(x)/Sat` for `x != 0`, and all four
//! `Sat/Sat` cells) are sound for free — `Nan` denotes everything — because
//! `div`'s one true indeterminate, `∞/∞`, is witnessed *only* by `Inf/Inf`
//! (both denotations singletons; the other genuine indeterminate, `0/0`, is
//! witnessed only by `Number(0)/Number(0)`, inside the excluded region). So
//! [`theorem_div_honest`] only has to work at `Inf/Inf`, and the remaining
//! soundness work is five families, several of them exact rather than
//! merely sound: [`lemma_div_sound_number_sat`] (`Number(x)/Sat`, exact `0`
//! at `x = 0`), [`lemma_div_sound_to_inf`] (`Number/Inf` and `Sat/Inf`,
//! exact `0` always: a finite value over an infinity), [`lemma_div_sound_sat_number`]
//! (`Sat/Number`, the real magnitude test), and [`lemma_div_sound_inf_number`]
//! / [`lemma_div_sound_inf_sat`] (an infinite numerator, sign-based, no `Nan`
//! at all — `§4`'s IEEE convention makes `±∞/0` defined).

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

/// `Sat`'s `Fin` is never the zero value. Duplicated from
/// `soundness_mul.rs`'s `lemma_sat_never_zero` (private there) rather than
/// exposed across files for one call site.
proof fn lemma_div_sat_never_zero(pos: bool, v: XR)
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

/// **Soundness** for `div`. See `soundness.rs`'s `add_sound`.
pub open spec fn div_sound(a: Q, b: Q, r: Q) -> bool {
    forall|u: XR, v: XR|
        xr_wf(u) && xr_wf(v) && denotes(a, u) && denotes(b, v) && xr_div(u, v).is_some()
            ==> #[trigger] denotes(r, xr_div(u, v).unwrap())
}

/// **Honesty** for `div`: within this file's scope (`Number × Number`
/// excluded), `∞/∞` is the only witnessable indeterminate.
pub open spec fn div_honest(a: Q, b: Q, r: Q) -> bool {
    (exists|u: XR, v: XR|
        xr_wf(u) && xr_wf(v) && denotes(a, u) && denotes(b, v) && xr_div(u, v).is_none())
        ==> r == Q::Nan
}

/// **`Number(x) / Sat`.** Exact `0` at `x = 0` (the true quotient is `0`
/// regardless of the divisor's actual value past the budget); `Nan`
/// otherwise, sound for free.
pub proof fn lemma_div_sound_number_sat(x: Rat, sat_pos: bool)
    requires
        x.wf(),
    ensures
        div_sound(
            Q::Number(x),
            if sat_pos { Q::PosSat } else { Q::NegSat },
            if x.n() == 0 { Q::Number(Rat::from_raw_spec(0, 1)) } else { Q::Nan },
        ),
{
    let b = if sat_pos { Q::PosSat } else { Q::NegSat };
    let r = if x.n() == 0 { Q::Number(Rat::from_raw_spec(0, 1)) } else { Q::Nan };
    if x.n() == 0 {
        assert forall|u: XR, v: XR|
            xr_wf(u) && xr_wf(v) && denotes(Q::Number(x), u) && denotes(b, v) && xr_div(u, v).is_some()
            implies #[trigger] denotes(r, xr_div(u, v).unwrap()) by {
            lemma_denotes_number_unique(x, u);
            match (u, v) {
                (XR::Fin(un, ud), XR::Fin(vn, vd)) => {
                    assert(un == 0) by (nonlinear_arith)
                        requires
                            un * x.d() == x.n() * ud,
                            x.n() == 0,
                            x.d() > 0,
                    ;
                    // `vn != 0`: `Sat`'s `Fin` is never zero.
                    if sat_pos {
                        assert(vn > 0) by (nonlinear_arith)
                            requires
                                vn > max_mag() * vd,
                                vd > 0,
                                max_mag() >= 0,
                        ;
                    } else {
                        assert(vn < 0) by (nonlinear_arith)
                            requires
                                vn < 0 - max_mag() * vd,
                                vd > 0,
                                max_mag() >= 0,
                        ;
                    }
                    Rat::lemma_from_raw_spec_components(0, 1);
                    // `xr_div`'s `Fin, Fin` arm with `vn > 0`: `Fin(un * vd, ud
                    // * vn)`; `un == 0` makes the numerator `0`.
                    if vn > 0 {
                        assert((un * vd) * 1 == 0 * (ud * vn)) by (nonlinear_arith)
                            requires
                                un == 0,
                        ;
                    } else {
                        assert((0 - un * vd) * 1 == 0 * (0 - ud * vn)) by (nonlinear_arith)
                            requires
                                un == 0,
                        ;
                    }
                },
                _ => {},
            }
        }
    }
}

/// **`Number / Inf`** and **`Sat / Inf`**: exact `0` — a finite value (`Sat`
/// denotes only finite reals) over an infinity.
pub proof fn lemma_div_sound_to_inf(a: Q, inf_pos: bool)
    requires
        a.wf(),
        a.spec_is_number() || a.spec_is_saturated(),
    ensures
        div_sound(a, if inf_pos { Q::PosInf } else { Q::NegInf }, Q::Number(Rat::from_raw_spec(0, 1))),
{
    let b = if inf_pos { Q::PosInf } else { Q::NegInf };
    let r = Q::Number(Rat::from_raw_spec(0, 1));
    assert forall|u: XR, v: XR|
        xr_wf(u) && xr_wf(v) && denotes(a, u) && denotes(b, v) && xr_div(u, v).is_some()
        implies #[trigger] denotes(r, xr_div(u, v).unwrap()) by {
        if inf_pos {
            lemma_denotes_posinf_unique(v);
        } else {
            lemma_denotes_neginf_unique(v);
        }
        Rat::lemma_from_raw_spec_components(0, 1);
        match u {
            XR::Fin(_un, _ud) => {
                // `xr_div`'s `Fin, Infinity` arm is unconditionally `Fin(0, 1)`.
                assert(0 * 1 == 0 * 1);
            },
            _ => {},
        }
    }
}

/// **`Sat / Number(y)`.** `y = 0` gives a signed infinity (`Sat` is
/// nonzero); `|y| <= 1` preserves saturation with the product-of-signs
/// rule; `|y| > 1` is `Nan`, sound for free.
pub proof fn lemma_div_sound_sat_number(sat_pos: bool, y: Rat)
    requires
        y.wf(),
    ensures
        div_sound(if sat_pos { Q::PosSat } else { Q::NegSat }, Q::Number(y), Q::spec_sat_div_number(sat_pos, y)),
{
    let a = if sat_pos { Q::PosSat } else { Q::NegSat };
    assert forall|u: XR, v: XR|
        xr_wf(u) && xr_wf(v) && denotes(a, u) && denotes(Q::Number(y), v) && xr_div(u, v).is_some()
        implies #[trigger] denotes(Q::spec_sat_div_number(sat_pos, y), xr_div(u, v).unwrap()) by {
        lemma_denotes_number_unique(y, v);
        match (u, v) {
            (XR::Fin(un, ud), XR::Fin(vn, vd)) => {
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
                if y.n() == 0 {
                    assert(vn == 0) by (nonlinear_arith)
                        requires
                            vn * y.d() == y.n() * vd,
                            y.n() == 0,
                            y.d() > 0,
                    ;
                    // `xr_div`'s `Fin, Fin` arm with `vn == 0`: a signed
                    // infinity matching `un`'s sign (`spec_sat_div_number`'s
                    // own `s == 0` branch reads the same sign off `y`).
                } else if y.n() > 0 {
                    assert(vn > 0) by (nonlinear_arith)
                        requires
                            vn * y.d() == y.n() * vd,
                            y.n() > 0,
                            y.d() > 0,
                            vd > 0,
                    ;
                    if y.n() <= y.d() {
                        assert(vn <= vd) by (nonlinear_arith)
                            requires
                                vn * y.d() == y.n() * vd,
                                y.n() <= y.d(),
                                vn > 0,
                                vd > 0,
                                y.d() > 0,
                        ;
                        // `xr_div`'s `vn > 0` branch: `Fin(un * vd, ud * vn)`.
                        // `0 < vn <= vd` and `un`'s magnitude past the
                        // budget carry straight through: `un * vd` is at
                        // least as far past `max_mag() * (ud * vn)` (in
                        // `un`'s sign) as `un * vn` already is.
                        if sat_pos {
                            assert(un * vd > max_mag() * (ud * vn)) by (nonlinear_arith)
                                requires
                                    un > max_mag() * ud,
                                    un > 0,
                                    ud > 0,
                                    vn > 0,
                                    vn <= vd,
                                    max_mag() >= 0,
                            ;
                        } else {
                            assert(un * vd < 0 - max_mag() * (ud * vn)) by (nonlinear_arith)
                                requires
                                    un < 0 - max_mag() * ud,
                                    un < 0,
                                    ud > 0,
                                    vn > 0,
                                    vn <= vd,
                                    max_mag() >= 0,
                            ;
                        }
                    }
                } else {
                    assert(vn < 0) by (nonlinear_arith)
                        requires
                            vn * y.d() == y.n() * vd,
                            y.n() < 0,
                            y.d() > 0,
                            vd > 0,
                    ;
                    if y.n() >= 0 - y.d() {
                        assert(0 - vd <= vn) by (nonlinear_arith)
                            requires
                                vn * y.d() == y.n() * vd,
                                y.n() >= 0 - y.d(),
                                vn < 0,
                                vd > 0,
                                y.d() > 0,
                        ;
                        // `xr_div`'s `vn < 0` branch: `Fin(-(un * vd), -(ud *
                        // vn))`, the mirror of the `vn > 0` case above with
                        // `vn` replaced by `-vn` (`0 < -vn <= vd`).
                        if sat_pos {
                            assert(0 - (un * vd) < 0 - max_mag() * (0 - (ud * vn))) by (nonlinear_arith)
                                requires
                                    un > max_mag() * ud,
                                    un > 0,
                                    ud > 0,
                                    vn < 0,
                                    0 - vd <= vn,
                                    max_mag() >= 0,
                            ;
                        } else {
                            assert(0 - (un * vd) > max_mag() * (0 - (ud * vn))) by (nonlinear_arith)
                                requires
                                    un < 0 - max_mag() * ud,
                                    un < 0,
                                    ud > 0,
                                    vn < 0,
                                    0 - vd <= vn,
                                    max_mag() >= 0,
                            ;
                        }
                    }
                }
            },
            _ => {},
        }
    }
}

/// **`Inf / Number(y)`.** Sign-based; `y = 0` is defined too (`§4`'s IEEE
/// convention), never `Nan`.
pub proof fn lemma_div_sound_inf_number(inf_pos: bool, y: Rat)
    requires
        y.wf(),
    ensures
        div_sound(
            if inf_pos { Q::PosInf } else { Q::NegInf },
            Q::Number(y),
            if y.n() < 0 { if inf_pos { Q::NegInf } else { Q::PosInf } } else { if inf_pos { Q::PosInf } else { Q::NegInf } },
        ),
{
    let a = if inf_pos { Q::PosInf } else { Q::NegInf };
    let r = if y.n() < 0 {
        if inf_pos { Q::NegInf } else { Q::PosInf }
    } else {
        if inf_pos { Q::PosInf } else { Q::NegInf }
    };
    assert forall|u: XR, v: XR|
        xr_wf(u) && xr_wf(v) && denotes(a, u) && denotes(Q::Number(y), v) && xr_div(u, v).is_some()
        implies #[trigger] denotes(r, xr_div(u, v).unwrap()) by {
        if inf_pos {
            lemma_denotes_posinf_unique(u);
        } else {
            lemma_denotes_neginf_unique(u);
        }
        lemma_denotes_number_unique(y, v);
        match v {
            XR::Fin(vn, vd) => {
                if y.n() < 0 {
                    assert(vn < 0) by (nonlinear_arith)
                        requires
                            vn * y.d() == y.n() * vd,
                            y.n() < 0,
                            y.d() > 0,
                            vd > 0,
                    ;
                } else {
                    assert(vn >= 0) by (nonlinear_arith)
                        requires
                            vn * y.d() == y.n() * vd,
                            y.n() >= 0,
                            y.d() > 0,
                            vd > 0,
                    ;
                }
            },
            _ => {},
        }
    }
}

/// **`Inf / Sat`.** Sign-based; `Sat` is never zero, no `Nan`.
pub proof fn lemma_div_sound_inf_sat(inf_pos: bool, sat_pos: bool)
    requires
        true,
    ensures
        div_sound(
            if inf_pos { Q::PosInf } else { Q::NegInf },
            if sat_pos { Q::PosSat } else { Q::NegSat },
            if inf_pos == sat_pos { Q::PosInf } else { Q::NegInf },
        ),
{
    let a = if inf_pos { Q::PosInf } else { Q::NegInf };
    let b = if sat_pos { Q::PosSat } else { Q::NegSat };
    let r = if inf_pos == sat_pos { Q::PosInf } else { Q::NegInf };
    assert forall|u: XR, v: XR|
        xr_wf(u) && xr_wf(v) && denotes(a, u) && denotes(b, v) && xr_div(u, v).is_some()
        implies #[trigger] denotes(r, xr_div(u, v).unwrap()) by {
        if inf_pos {
            lemma_denotes_posinf_unique(u);
        } else {
            lemma_denotes_neginf_unique(u);
        }
        match v {
            XR::Fin(vn, vd) => {
                if sat_pos {
                    assert(vn > 0) by (nonlinear_arith)
                        requires
                            vn > max_mag() * vd,
                            vd > 0,
                            max_mag() >= 0,
                    ;
                } else {
                    assert(vn < 0) by (nonlinear_arith)
                        requires
                            vn < 0 - max_mag() * vd,
                            vd > 0,
                            max_mag() >= 0,
                    ;
                }
            },
            _ => {},
        }
    }
}

/// **`Q::div` is sound**, restricted to the special-value propagation
/// cells (`Number × Number`, including its zero-divisor sub-case, excluded —
/// see the module doc).
pub proof fn theorem_div_sound(a: Q, b: Q)
    requires
        a.wf(),
        b.wf(),
        !(a.spec_is_number() && b.spec_is_number()),
    ensures
        div_sound(a, b, Q::spec_div(a, b)),
{
    match (a, b) {
        (Q::Nan, _) | (_, Q::Nan) => {},
        (Q::Number(_), Q::Number(_)) => {
            assert(false);
        },
        (Q::Number(x), Q::PosSat) => {
            lemma_div_sound_number_sat(x, true);
        },
        (Q::Number(x), Q::NegSat) => {
            lemma_div_sound_number_sat(x, false);
        },
        (Q::Number(_), Q::PosInf) => {
            lemma_div_sound_to_inf(a, true);
        },
        (Q::Number(_), Q::NegInf) => {
            lemma_div_sound_to_inf(a, false);
        },
        (Q::PosSat, Q::Number(y)) => {
            lemma_div_sound_sat_number(true, y);
        },
        (Q::NegSat, Q::Number(y)) => {
            lemma_div_sound_sat_number(false, y);
        },
        (Q::PosSat, Q::PosSat) | (Q::PosSat, Q::NegSat) | (Q::NegSat, Q::PosSat)
        | (Q::NegSat, Q::NegSat) => {
            // `Q::spec_div` gives `Nan` here; `denotes(Nan, _)` is `true`.
        },
        (Q::PosSat, Q::PosInf) | (Q::NegSat, Q::PosInf) => {
            lemma_div_sound_to_inf(a, true);
        },
        (Q::PosSat, Q::NegInf) | (Q::NegSat, Q::NegInf) => {
            lemma_div_sound_to_inf(a, false);
        },
        (Q::PosInf, Q::Number(y)) => {
            lemma_div_sound_inf_number(true, y);
        },
        (Q::NegInf, Q::Number(y)) => {
            lemma_div_sound_inf_number(false, y);
        },
        (Q::PosInf, Q::PosSat) => {
            lemma_div_sound_inf_sat(true, true);
        },
        (Q::PosInf, Q::NegSat) => {
            lemma_div_sound_inf_sat(true, false);
        },
        (Q::NegInf, Q::PosSat) => {
            lemma_div_sound_inf_sat(false, true);
        },
        (Q::NegInf, Q::NegSat) => {
            lemma_div_sound_inf_sat(false, false);
        },
        (Q::PosInf, Q::PosInf) | (Q::PosInf, Q::NegInf) | (Q::NegInf, Q::PosInf)
        | (Q::NegInf, Q::NegInf) => {
            // `Q::spec_div` gives `Nan` here; `denotes(Nan, _)` is `true`.
        },
    }
}

/// **`Q::div` is honest.** Within this file's scope, `∞/∞` is the only
/// witnessable indeterminate, and it is witnessed only by `Inf/Inf` — both
/// denotations singletons.
pub proof fn theorem_div_honest(a: Q, b: Q)
    requires
        a.wf(),
        b.wf(),
        !(a.spec_is_number() && b.spec_is_number()),
    ensures
        div_honest(a, b, Q::spec_div(a, b)),
{
    if exists|u: XR, v: XR|
        xr_wf(u) && xr_wf(v) && denotes(a, u) && denotes(b, v) && xr_div(u, v).is_none() {
        let (u, v): (XR, XR) = choose|u: XR, v: XR|
            xr_wf(u) && xr_wf(v) && denotes(a, u) && denotes(b, v) && xr_div(u, v).is_none();
        match (a, b) {
            (Q::Nan, _) | (_, Q::Nan) => {
                assert(Q::spec_div(a, b) == Q::Nan);
            },
            (Q::PosInf, Q::PosInf) | (Q::PosInf, Q::NegInf) | (Q::NegInf, Q::PosInf)
            | (Q::NegInf, Q::NegInf) => {
                assert(Q::spec_div(a, b) == Q::Nan);
            },
            _ => {
                // Every other pair: show `xr_div(u, v).is_some()`,
                // contradicting the `choose`d witness.
                // At most one of `a`, `b` is `Number` (the hypothesis
                // excludes both); the other is `Sat` or `Inf`, and `Sat`'s
                // `Fin` is never zero. So whichever side is `Fin`-shaped and
                // not `Number`, its value is pinned nonzero here — enough to
                // rule out `xr_div`'s only `Fin, Fin` `None` case (`0 / 0`).
                match a {
                    Q::Number(x) => {
                        lemma_denotes_number_unique(x, u);
                    },
                    Q::PosSat => {
                        lemma_div_sat_never_zero(true, u);
                    },
                    Q::NegSat => {
                        lemma_div_sat_never_zero(false, u);
                    },
                    Q::PosInf => {
                        lemma_denotes_posinf_unique(u);
                    },
                    Q::NegInf => {
                        lemma_denotes_neginf_unique(u);
                    },
                    Q::Nan => {},
                }
                match b {
                    Q::Number(y) => {
                        lemma_denotes_number_unique(y, v);
                    },
                    Q::PosSat => {
                        lemma_div_sat_never_zero(true, v);
                    },
                    Q::NegSat => {
                        lemma_div_sat_never_zero(false, v);
                    },
                    Q::PosInf => {
                        lemma_denotes_posinf_unique(v);
                    },
                    Q::NegInf => {
                        lemma_denotes_neginf_unique(v);
                    },
                    Q::Nan => {},
                }
                match (u, v) {
                    (XR::Fin(_, _), XR::Fin(_, _)) => {
                        assert(xr_div(u, v).is_some());
                    },
                    (XR::PosInfinity, XR::Fin(_, _)) | (XR::NegInfinity, XR::Fin(_, _)) => {
                        assert(xr_div(u, v).is_some());
                    },
                    (XR::Fin(_, _), XR::PosInfinity) | (XR::Fin(_, _), XR::NegInfinity) => {
                        assert(xr_div(u, v).is_some());
                    },
                    (XR::PosInfinity, XR::PosInfinity) | (XR::PosInfinity, XR::NegInfinity)
                    | (XR::NegInfinity, XR::PosInfinity) | (XR::NegInfinity, XR::NegInfinity) => {
                        assert(false);
                    },
                }
                assert(false);
            },
        }
    }
}

} // verus!
