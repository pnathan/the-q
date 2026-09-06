//! Issue #28: the containment obligation for [`crate::ext::Q::add`], proven
//! against [`crate::denote`]'s ghost `XR` model, restricted to the
//! special-value propagation cells — at least one operand is not a `Number`.
//!
//! The `Number × Number -> Number` cell is deliberately **not** covered here:
//! its containment is `R1`–`R4` (`VERIFICATION.md` V4, `crate::round`),
//! already proven, and a literal containment statement on it would demand
//! that rounding never round, which is false exactly when it does. This
//! file's scope is the propagation table (issue #26 §5/§28 together): the
//! cells where a `Sat`, an `Inf`, or a `Nan` enters or leaves.
//!
//! The proof is organized by how much of the 5×5 non-`Nan` state space one
//! lemma settles, not by table cell, because `Q::add`'s own table is already
//! symmetric and dominance-shaped:
//!
//! * [`lemma_add_sound_symm`] turns a proof for `(a, b)` into one for `(b,
//!   a)` for free, using [`crate::laws_q::theorem_q_add_commutative`] and
//!   [`lemma_xr_add_comm`] — halving the casework the table's symmetric
//!   layout already implies.
//! * [`lemma_add_sound_posinf_dominates`] and its `NegInf` mirror settle
//!   *every* cell where one operand is a same-signed-or-absent infinity in
//!   one shot: an infinity's denotation is a singleton, so once the other
//!   operand is confirmed not to be the opposite infinity, its own shape
//!   (`Number`, `Sat`, or the same infinity) never enters the argument.
//! * What is left — `Number + Sat` and `Sat + Sat` (same sign) — is the two
//!   genuine magnitude arguments, [`lemma_add_sound_number_sat`] and
//!   [`lemma_add_sound_sat_sat_same_sign`].

use verus_builtin_macros::verus;

#[allow(unused_imports)]
use verus_builtin::*;
#[allow(unused_imports)]
use vstd::prelude::*;

use crate::denote::{
    XR,
    denotes,
    lemma_denotes_number_unique,
    lemma_denotes_neginf_unique,
    lemma_denotes_posinf_unique,
    lemma_number_not_saturated,
    xr_add,
    xr_eq,
    xr_wf,
};
use crate::ext::Q;
use crate::model::{abs_int, max_mag};
use crate::types::Rat;

verus! {

// ---------------------------------------------------------------------------
// The two properties
// ---------------------------------------------------------------------------

/// **Soundness**: every value the true addition of a value `a` denotes and a
/// value `b` denotes could produce is inside `r`'s denotation. Never
/// references `Q::spec_add` — see the module doc on `laws_q.rs`'s Firewall
/// discipline (this is the specification a mirror shaped like the table
/// could not check).
pub open spec fn add_sound(a: Q, b: Q, r: Q) -> bool {
    forall|u: XR, v: XR|
        xr_wf(u) && xr_wf(v) && denotes(a, u) && denotes(b, v) && xr_add(u, v).is_some()
            ==> #[trigger] denotes(r, xr_add(u, v).unwrap())
}

/// **Honesty**: if `a` and `b` can witness `add`'s one true indeterminate
/// (`∞ + (-∞)`), `r` must actually *be* `Nan` — a function could be sound
/// while quietly returning some other, larger-denoting state; this rules
/// that out.
pub open spec fn add_honest(a: Q, b: Q, r: Q) -> bool {
    (exists|u: XR, v: XR|
        xr_wf(u) && xr_wf(v) && denotes(a, u) && denotes(b, v) && xr_add(u, v).is_none())
        ==> r == Q::Nan
}

// ---------------------------------------------------------------------------
// Generic infrastructure: commutativity and its lift
// ---------------------------------------------------------------------------

/// `xr_add` is commutative. The `Fin, Fin` case needs multiplication
/// commutativity for its denominator; every other case is already written
/// symmetrically in [`xr_add`]'s own match.
pub proof fn lemma_xr_add_comm(u: XR, v: XR)
    requires
        xr_wf(u),
        xr_wf(v),
    ensures
        xr_add(u, v) == xr_add(v, u),
{
    match (u, v) {
        (XR::Fin(un, ud), XR::Fin(vn, vd)) => {
            assert(ud * vd == vd * ud) by (nonlinear_arith);
        },
        _ => {},
    }
}

/// A soundness proof for `(a, b)` lifts to one for `(b, a)`, using `add`'s
/// commutativity at the `Q` level and `xr_add`'s at the `XR` level.
pub proof fn lemma_add_sound_symm(a: Q, b: Q, r: Q)
    requires
        a.wf(),
        b.wf(),
        add_sound(a, b, r),
    ensures
        add_sound(b, a, r),
{
    assert forall|u: XR, v: XR|
        xr_wf(u) && xr_wf(v) && denotes(b, u) && denotes(a, v) && xr_add(u, v).is_some()
        implies #[trigger] denotes(r, xr_add(u, v).unwrap()) by {
        lemma_xr_add_comm(u, v);
    }
}

// ---------------------------------------------------------------------------
// Dominance: one operand is (the absence of) an infinity of a fixed sign
// ---------------------------------------------------------------------------

/// Nothing but `NegInf` or `Nan` denotes `NegInfinity`: `Number`'s and
/// `Sat`'s denotations are `Fin`-shaped by construction, and `PosInf`'s is
/// the unrelated singleton `PosInfinity`.
pub proof fn lemma_not_neginf_excludes_neginfinity(b: Q, v: XR)
    requires
        b.wf(),
        b != Q::NegInf,
        b != Q::Nan,
        denotes(b, v),
    ensures
        v != XR::NegInfinity,
{
    if v == XR::NegInfinity {
        match b {
            Q::Number(x) => {
                assert(denotes(b, v) == xr_eq(XR::NegInfinity, XR::Fin(x.n(), x.d())));
                assert(!xr_eq(XR::NegInfinity, XR::Fin(x.n(), x.d())));
            },
            Q::PosSat => {
                assert(!denotes(Q::PosSat, XR::NegInfinity));
            },
            Q::NegSat => {
                assert(!denotes(Q::NegSat, XR::NegInfinity));
            },
            Q::PosInf => {
                lemma_denotes_posinf_unique(v);
            },
            Q::NegInf | Q::Nan => {},
        }
        assert(false);
    }
}

/// Mirror of [`lemma_not_neginf_excludes_neginfinity`].
pub proof fn lemma_not_posinf_excludes_posinfinity(b: Q, v: XR)
    requires
        b.wf(),
        b != Q::PosInf,
        b != Q::Nan,
        denotes(b, v),
    ensures
        v != XR::PosInfinity,
{
    if v == XR::PosInfinity {
        match b {
            Q::Number(x) => {
                assert(denotes(b, v) == xr_eq(XR::PosInfinity, XR::Fin(x.n(), x.d())));
                assert(!xr_eq(XR::PosInfinity, XR::Fin(x.n(), x.d())));
            },
            Q::PosSat => {
                assert(!denotes(Q::PosSat, XR::PosInfinity));
            },
            Q::NegSat => {
                assert(!denotes(Q::NegSat, XR::PosInfinity));
            },
            Q::NegInf => {
                lemma_denotes_neginf_unique(v);
            },
            Q::PosInf | Q::Nan => {},
        }
        assert(false);
    }
}

/// **`PosInf` dominates.** For *any* `b` (including `NegInf`: there the
/// hypothesis `xr_add(u, v).is_some()` is simply never satisfiable, and the
/// statement holds vacuously — `spec_add(PosInf, NegInf)` is `Nan`, not
/// `PosInf`, and it is [`theorem_add_honest`] that rules the vacuous cell
/// out, not this lemma), the sum is sound as `PosInf` whenever it is defined
/// at all: `a`'s denotation is the singleton `PosInfinity`, and `xr_add`'s
/// only `None` case with a `PosInfinity` first argument is `NegInfinity`
/// second.
pub proof fn lemma_add_sound_posinf_dominates(b: Q)
    requires
        b.wf(),
    ensures
        add_sound(Q::PosInf, b, Q::PosInf),
{
    assert forall|u: XR, v: XR|
        xr_wf(u) && xr_wf(v) && denotes(Q::PosInf, u) && denotes(b, v) && xr_add(u, v).is_some()
        implies #[trigger] denotes(Q::PosInf, xr_add(u, v).unwrap()) by {
        lemma_denotes_posinf_unique(u);
        // `u == PosInfinity`; `xr_add`'s only `None` arm with `PosInfinity`
        // first is `(PosInfinity, NegInfinity)`, ruled out by the hypothesis
        // `xr_add(u, v).is_some()` itself.
        assert(xr_add(u, v) == Some(XR::PosInfinity));
    }
}

/// Mirror of [`lemma_add_sound_posinf_dominates`].
pub proof fn lemma_add_sound_neginf_dominates(b: Q)
    requires
        b.wf(),
    ensures
        add_sound(Q::NegInf, b, Q::NegInf),
{
    assert forall|u: XR, v: XR|
        xr_wf(u) && xr_wf(v) && denotes(Q::NegInf, u) && denotes(b, v) && xr_add(u, v).is_some()
        implies #[trigger] denotes(Q::NegInf, xr_add(u, v).unwrap()) by {
        lemma_denotes_neginf_unique(u);
        assert(xr_add(u, v) == Some(XR::NegInfinity));
    }
}

// ---------------------------------------------------------------------------
// The two genuine magnitude arguments
// ---------------------------------------------------------------------------

/// **`Number(x) + Sat`.** Sound as the same-signed `Sat` when `x`'s sign
/// agrees (or is zero); the opposite sign gives `Nan`, sound for free.
pub proof fn lemma_add_sound_number_sat(x: Rat, sat_pos: bool)
    requires
        x.wf(),
    ensures
        add_sound(Q::Number(x), if sat_pos { Q::PosSat } else { Q::NegSat }, Q::spec_number_plus_sat(x, sat_pos)),
{
    let b = if sat_pos { Q::PosSat } else { Q::NegSat };
    assert forall|u: XR, v: XR|
        xr_wf(u) && xr_wf(v) && denotes(Q::Number(x), u) && denotes(b, v) && xr_add(u, v).is_some()
        implies #[trigger] denotes(Q::spec_number_plus_sat(x, sat_pos), xr_add(u, v).unwrap()) by {
        lemma_denotes_number_unique(x, u);
        // `u`'s shape: `xr_eq(u, Fin(x.n(), x.d()))` forces `u` itself `Fin`,
        // since no other `XR` constructor is ever `xr_eq` to a `Fin`.
        let un = if let XR::Fin(n, _d) = u { n } else { 0 };
        let ud = if let XR::Fin(_n, d) = u { d } else { 1 };
        if sat_pos {
            if x.n() >= 0 {
                assert(un >= 0) by (nonlinear_arith)
                    requires
                        un * x.d() == x.n() * ud,
                        x.n() >= 0,
                        x.d() > 0,
                        ud > 0,
                ;
            } else {
            }
        } else {
            if x.n() <= 0 {
                assert(un <= 0) by (nonlinear_arith)
                    requires
                        un * x.d() == x.n() * ud,
                        x.n() <= 0,
                        x.d() > 0,
                        ud > 0,
                ;
            } else {
            }
        }
        match v {
            XR::Fin(vn, vd) => {
                if sat_pos {
                    if x.n() >= 0 {
                        assert(un * vd + vn * ud > max_mag() * (ud * vd)) by (nonlinear_arith)
                            requires
                                un >= 0,
                                vn > max_mag() * vd,
                                ud > 0,
                                vd > 0,
                        ;
                    }
                } else {
                    if x.n() <= 0 {
                        assert(un * vd + vn * ud < 0 - max_mag() * (ud * vd)) by (nonlinear_arith)
                            requires
                                un <= 0,
                                vn < 0 - max_mag() * vd,
                                ud > 0,
                                vd > 0,
                        ;
                    }
                }
            },
            _ => {},
        }
    }
}

/// **`Sat + Sat`, same sign.** Reinforces: the sum of two magnitudes each
/// past the budget is further past it.
pub proof fn lemma_add_sound_sat_sat_same_sign(pos: bool)
    requires
        true,
    ensures
        add_sound(
            if pos { Q::PosSat } else { Q::NegSat },
            if pos { Q::PosSat } else { Q::NegSat },
            if pos { Q::PosSat } else { Q::NegSat },
        ),
{
    let s = if pos { Q::PosSat } else { Q::NegSat };
    assert forall|u: XR, v: XR|
        xr_wf(u) && xr_wf(v) && denotes(s, u) && denotes(s, v) && xr_add(u, v).is_some()
        implies #[trigger] denotes(s, xr_add(u, v).unwrap()) by {
        match (u, v) {
            (XR::Fin(un, ud), XR::Fin(vn, vd)) => {
                if pos {
                    assert(un * vd + vn * ud > max_mag() * (ud * vd)) by (nonlinear_arith)
                        requires
                            un > max_mag() * ud,
                            vn > max_mag() * vd,
                            ud > 0,
                            vd > 0,
                            max_mag() >= 0,
                    ;
                } else {
                    assert(un * vd + vn * ud < 0 - max_mag() * (ud * vd)) by (nonlinear_arith)
                        requires
                            un < 0 - max_mag() * ud,
                            vn < 0 - max_mag() * vd,
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

// ---------------------------------------------------------------------------
// Assembly
// ---------------------------------------------------------------------------

/// **`Q::add` is sound**, restricted to the special-value propagation cells
/// (`R1`–`R4` already cover `Number × Number -> Number`).
pub proof fn theorem_add_sound(a: Q, b: Q)
    requires
        a.wf(),
        b.wf(),
        !(a.spec_is_number() && b.spec_is_number()),
    ensures
        add_sound(a, b, Q::spec_add(a, b)),
{
    match (a, b) {
        (Q::Nan, _) | (_, Q::Nan) => {
            // `denotes(Nan, _)` is `true`: nothing to show.
        },
        (Q::Number(_), Q::Number(_)) => {
            assert(false);
        },
        (Q::PosInf, Q::NegInf) | (Q::NegInf, Q::PosInf) => {
            // `Q::spec_add` gives `Nan` here; `denotes(Nan, _)` is `true`.
        },
        (Q::PosInf, _) => {
            lemma_add_sound_posinf_dominates(b);
        },
        (Q::NegInf, _) => {
            lemma_add_sound_neginf_dominates(b);
        },
        (_, Q::PosInf) => {
            lemma_add_sound_posinf_dominates(a);
            lemma_add_sound_symm(Q::PosInf, a, Q::PosInf);
        },
        (_, Q::NegInf) => {
            lemma_add_sound_neginf_dominates(a);
            lemma_add_sound_symm(Q::NegInf, a, Q::NegInf);
        },
        (Q::Number(x), Q::PosSat) => {
            lemma_add_sound_number_sat(x, true);
        },
        (Q::Number(x), Q::NegSat) => {
            lemma_add_sound_number_sat(x, false);
        },
        (Q::PosSat, Q::Number(y)) => {
            lemma_add_sound_number_sat(y, true);
            lemma_add_sound_symm(Q::Number(y), Q::PosSat, Q::spec_number_plus_sat(y, true));
        },
        (Q::NegSat, Q::Number(y)) => {
            lemma_add_sound_number_sat(y, false);
            lemma_add_sound_symm(Q::Number(y), Q::NegSat, Q::spec_number_plus_sat(y, false));
        },
        (Q::PosSat, Q::PosSat) => {
            lemma_add_sound_sat_sat_same_sign(true);
        },
        (Q::NegSat, Q::NegSat) => {
            lemma_add_sound_sat_sat_same_sign(false);
        },
        (Q::PosSat, Q::NegSat) | (Q::NegSat, Q::PosSat) => {
            // `Q::spec_add` gives `Nan` here; `denotes(Nan, _)` is `true`.
        },
    }
}

/// **`Q::add` is honest.** `add`'s one indeterminate, `∞ + (-∞)`, can only be
/// witnessed when `a` is `PosInf`/`NegInf` and `b` the opposite — both cells
/// already produce `Nan`. Everywhere else, `xr_add`'s totality on
/// non-opposite-infinity pairs rules the antecedent out.
pub proof fn theorem_add_honest(a: Q, b: Q)
    requires
        a.wf(),
        b.wf(),
    ensures
        add_honest(a, b, Q::spec_add(a, b)),
{
    if Q::spec_add(a, b) != Q::Nan {
        assert forall|u: XR, v: XR|
            xr_wf(u) && xr_wf(v) && denotes(a, u) && denotes(b, v)
            implies #[trigger] xr_add(u, v).is_some() by {
            match (a, b) {
                (Q::PosInf, Q::NegInf) | (Q::NegInf, Q::PosInf) => {
                    // `spec_add` is `Nan` here, contradicting the outer `if`.
                    assert(false);
                },
                (Q::PosInf, _) => {
                    assert(b != Q::Nan) by {
                        if b == Q::Nan {
                            assert(Q::spec_add(a, b) == Q::Nan);
                        }
                    }
                    lemma_not_neginf_excludes_neginfinity(b, v);
                    lemma_denotes_posinf_unique(u);
                },
                (Q::NegInf, _) => {
                    assert(b != Q::Nan) by {
                        if b == Q::Nan {
                            assert(Q::spec_add(a, b) == Q::Nan);
                        }
                    }
                    lemma_not_posinf_excludes_posinfinity(b, v);
                    lemma_denotes_neginf_unique(u);
                },
                (_, Q::PosInf) => {
                    assert(a != Q::Nan) by {
                        if a == Q::Nan {
                            assert(Q::spec_add(a, b) == Q::Nan);
                        }
                    }
                    lemma_not_neginf_excludes_neginfinity(a, u);
                    lemma_denotes_posinf_unique(v);
                },
                (_, Q::NegInf) => {
                    assert(a != Q::Nan) by {
                        if a == Q::Nan {
                            assert(Q::spec_add(a, b) == Q::Nan);
                        }
                    }
                    lemma_not_posinf_excludes_posinfinity(a, u);
                    lemma_denotes_neginf_unique(v);
                },
                _ => {},
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Necessity (pilot): `Nan` is not a lazy answer at `PosSat + NegSat`
//
// Soundness alone is satisfiable by `Nan` everywhere (it denotes every
// value), so it cannot be the whole obligation. Honesty rules `Nan` in at
// the one cell with no defined witness at all (`PosInf + NegInf`, both
// singleton denotations, `xr_add` already `None`). `PosSat + NegSat` is the
// complementary case: witnesses exist and their sums *are* defined, yet no
// single non-`Nan` state can be sound for both at once. Two sums that
// straddle zero (one negative, one positive) rule out every other variant:
// `Number` cannot equal two different values at once, `PosSat`/`NegSat`
// each demand a fixed sign, and `PosInf`/`NegInf` are never finite. This one
// cell is the pattern; it is not repeated for every `Nan` cell of `mul` and
// `div` (documented as a scoping decision, `VERIFICATION.md`).
// ---------------------------------------------------------------------------

/// If `r` is sound for `PosSat + NegSat`, `r` is `Nan` — no tighter answer
/// is sound for both of two witness pairs whose sums straddle zero.
pub proof fn theorem_add_nan_necessary_sat_sat_opposite(r: Q)
    requires
        r.wf(),
        add_sound(Q::PosSat, Q::NegSat, r),
    ensures
        r == Q::Nan,
{
    let u1 = XR::Fin(max_mag() + 1, 1);
    let v1 = XR::Fin(0 - (max_mag() + 2), 1);
    let u2 = XR::Fin(max_mag() + 5, 1);
    let v2 = XR::Fin(0 - (max_mag() + 2), 1);
    assert(xr_wf(u1) && xr_wf(v1));
    assert(xr_wf(u2) && xr_wf(v2));
    assert(denotes(Q::PosSat, u1));
    assert(denotes(Q::NegSat, v1));
    assert(denotes(Q::PosSat, u2));
    assert(denotes(Q::NegSat, v2));
    assert(xr_add(u1, v1) == Some(XR::Fin(0 - 1, 1)));
    assert(xr_add(u2, v2) == Some(XR::Fin(3, 1)));
    assert(denotes(r, xr_add(u1, v1).unwrap()));
    assert(denotes(r, xr_add(u2, v2).unwrap()));
    assert(denotes(r, XR::Fin(0 - 1, 1)));
    assert(denotes(r, XR::Fin(3, 1)));
    if r != Q::Nan {
        match r {
            Q::Number(x) => {
                assert(0 - 1 * x.d() == x.n() * 1);
                assert(3 * x.d() == x.n() * 1);
                assert(x.d() == 0) by (nonlinear_arith)
                    requires
                        0 - x.d() == x.n(),
                        3 * x.d() == x.n(),
                ;
                assert(false);
            },
            Q::PosSat => {
                assert(false);
            },
            Q::NegSat => {
                assert(false);
            },
            Q::PosInf | Q::NegInf => {
                assert(false);
            },
            Q::Nan => {},
        }
    }
}

} // verus!
