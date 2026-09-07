//! The true-value model behind issue #26 §2, and the containment obligation
//! from issue #28: `{x ⊕ y : x ∈ ⟦a⟧, y ∈ ⟦b⟧} ⊆ ⟦op(a, b)⟧` for every `Q`
//! operation.
//!
//! `XR` ("extended real", ghost-only) is the true-value domain: a finite
//! rational or a signed infinity. It has **three** constructors, deliberately
//! never five: no `Sat`, no `Nan`. A `Sat` constructor would smuggle `Q`'s own
//! state machine into the "true value" domain, and every lemma below would
//! risk restating the implementation rather than checking it against
//! something independent — the trap this crate has hit once already (the
//! comment on `crate::ext::Q::recip`). `denotes` is the *one* place
//! allowed to pattern-match `Q`'s variants against `XR`'s; it must be written
//! with the literal `n > max_mag() * d` test and never with
//! `crate::model::magnitude_fits`, so that a shared mistake between this
//! file and `ext.rs`'s classification cannot cancel itself out.
//!
//! The obligation has three parts, and only the first is trivially
//! satisfiable (by `Nan` everywhere, which denotes every value):
//!
//! * **soundness** (`add_sound` and its `mul`/`div` counterparts in
//!   `laws_q.rs`): every value the true operation could have produced is
//!   inside the result's denotation.
//! * **honesty** (`add_honest`): when the operands can witness a genuine
//!   indeterminate (`∞ − ∞`, `0 · ∞`, `0/0`), the result must actually *be*
//!   `Nan`, not merely sound while reporting something else.
//! * **necessity**: `Nan` is not returned where a strictly smaller state
//!   would have been equally sound — proven per cell in `laws_q.rs`, because
//!   it needs concrete witness values, not a quantified statement.

use verus_builtin_macros::verus;

#[allow(unused_imports)]
use verus_builtin::*;
#[allow(unused_imports)]
use vstd::prelude::*;

#[allow(unused_imports)]
use crate::ext::*;
#[allow(unused_imports)]
use crate::model::*;
#[allow(unused_imports)]
use crate::types::*;

verus! {

/// A true value: a finite rational `n / d` (`d > 0`, not required to be
/// canonical — `XR::Fin(1, 2)` and `XR::Fin(2, 4)` are the same real, related
/// by `xr_eq`), or a signed infinity.
pub enum XR {
    Fin(int, int),
    PosInfinity,
    NegInfinity,
}

/// `v` is well-formed: a finite payload has a positive denominator.
pub open spec fn xr_wf(v: XR) -> bool {
    match v {
        XR::Fin(_n, d) => d > 0,
        _ => true,
    }
}

/// Real equality of two `XR`s, cross-multiplied because `Fin` is not
/// canonical.
pub open spec fn xr_eq(u: XR, v: XR) -> bool {
    match (u, v) {
        (XR::Fin(un, ud), XR::Fin(vn, vd)) => un * vd == vn * ud,
        (XR::PosInfinity, XR::PosInfinity) => true,
        (XR::NegInfinity, XR::NegInfinity) => true,
        _ => false,
    }
}

/// Whether `v` is the real number zero.
pub open spec fn xr_is_zero(v: XR) -> bool {
    match v {
        XR::Fin(n, _d) => n == 0,
        _ => false,
    }
}

/// `-v`, total and exact.
pub open spec fn xr_neg(v: XR) -> XR {
    match v {
        XR::Fin(n, d) => XR::Fin(-n, d),
        XR::PosInfinity => XR::NegInfinity,
        XR::NegInfinity => XR::PosInfinity,
    }
}

/// `u + v`, partial: `None` exactly at `∞ + (-∞)` and its mirror — the one
/// true indeterminate `add` can reach.
pub open spec fn xr_add(u: XR, v: XR) -> Option<XR> {
    match (u, v) {
        (XR::Fin(un, ud), XR::Fin(vn, vd)) => Some(XR::Fin(un * vd + vn * ud, ud * vd)),
        (XR::PosInfinity, XR::NegInfinity) => None,
        (XR::NegInfinity, XR::PosInfinity) => None,
        (XR::PosInfinity, _) => Some(XR::PosInfinity),
        (XR::NegInfinity, _) => Some(XR::NegInfinity),
        (_, XR::PosInfinity) => Some(XR::PosInfinity),
        (_, XR::NegInfinity) => Some(XR::NegInfinity),
    }
}

/// `u - v`, defined as `u + (-v)` rather than cased separately, so that
/// `sub`'s soundness follows from `add`'s and `xr_neg`'s for free.
pub open spec fn xr_sub(u: XR, v: XR) -> Option<XR> {
    xr_add(u, xr_neg(v))
}

/// `u * v`, partial: `None` exactly at `0 · ±∞` and its mirror.
pub open spec fn xr_mul(u: XR, v: XR) -> Option<XR> {
    match (u, v) {
        (XR::Fin(un, ud), XR::Fin(vn, vd)) => Some(XR::Fin(un * vn, ud * vd)),
        (XR::PosInfinity, XR::Fin(vn, _vd)) => if vn == 0 {
            None
        } else if vn > 0 {
            Some(XR::PosInfinity)
        } else {
            Some(XR::NegInfinity)
        },
        (XR::NegInfinity, XR::Fin(vn, _vd)) => if vn == 0 {
            None
        } else if vn > 0 {
            Some(XR::NegInfinity)
        } else {
            Some(XR::PosInfinity)
        },
        (XR::Fin(un, _ud), XR::PosInfinity) => if un == 0 {
            None
        } else if un > 0 {
            Some(XR::PosInfinity)
        } else {
            Some(XR::NegInfinity)
        },
        (XR::Fin(un, _ud), XR::NegInfinity) => if un == 0 {
            None
        } else if un > 0 {
            Some(XR::NegInfinity)
        } else {
            Some(XR::PosInfinity)
        },
        (XR::PosInfinity, XR::PosInfinity) => Some(XR::PosInfinity),
        (XR::PosInfinity, XR::NegInfinity) => Some(XR::NegInfinity),
        (XR::NegInfinity, XR::PosInfinity) => Some(XR::NegInfinity),
        (XR::NegInfinity, XR::NegInfinity) => Some(XR::PosInfinity),
    }
}

/// `u / v`, partial: `None` exactly at `0/0` and `±∞ / ±∞`.
pub open spec fn xr_div(u: XR, v: XR) -> Option<XR> {
    match (u, v) {
        (XR::Fin(un, ud), XR::Fin(vn, vd)) => if vn == 0 {
            if un == 0 {
                None
            } else if un > 0 {
                Some(XR::PosInfinity)
            } else {
                Some(XR::NegInfinity)
            }
        } else if vn > 0 {
            Some(XR::Fin(un * vd, ud * vn))
        } else {
            Some(XR::Fin(0 - un * vd, 0 - ud * vn))
        },
        (XR::PosInfinity, XR::Fin(vn, _vd)) => if vn < 0 {
            Some(XR::NegInfinity)
        } else {
            Some(XR::PosInfinity)
        },
        (XR::NegInfinity, XR::Fin(vn, _vd)) => if vn < 0 {
            Some(XR::PosInfinity)
        } else {
            Some(XR::NegInfinity)
        },
        (XR::Fin(_un, _ud), XR::PosInfinity) => Some(XR::Fin(0, 1)),
        (XR::Fin(_un, _ud), XR::NegInfinity) => Some(XR::Fin(0, 1)),
        (XR::PosInfinity, XR::PosInfinity) => None,
        (XR::PosInfinity, XR::NegInfinity) => None,
        (XR::NegInfinity, XR::PosInfinity) => None,
        (XR::NegInfinity, XR::NegInfinity) => None,
    }
}

/// The image of a `Q` state under issue #26 §2's table, restated as ghost
/// values Verus can quantify over. This is the *one* restatement of the
/// table the design permits — `add_sound` and its counterparts are what
/// checks it, since a `Nan`-everywhere spec would make containment trivially
/// true. `PosSat`/`NegSat` are written with the literal `max_mag() * d`
/// inequality, not `!magnitude_fits`, on purpose: see the module doc.
pub open spec fn denotes(q: Q, v: XR) -> bool {
    match q {
        Q::Number(x) => xr_eq(v, XR::Fin(x.n(), x.d())),
        Q::PosSat => match v {
            XR::Fin(n, d) => n > max_mag() * d,
            _ => false,
        },
        Q::NegSat => match v {
            XR::Fin(n, d) => n < 0 - max_mag() * d,
            _ => false,
        },
        Q::PosInf => match v {
            XR::PosInfinity => true,
            _ => false,
        },
        Q::NegInf => match v {
            XR::NegInfinity => true,
            _ => false,
        },
        Q::Nan => true,
    }
}

// ---------------------------------------------------------------------------
// N1 — inhabitation: every wf `Q` denotes at least one wf `XR`.
//
// The cheapest check and the one that catches the worst mistake: if some
// variant's denotation were secretly empty, every "soundness"/"honesty"
// statement about it would be vacuously true and would prove nothing.
// ---------------------------------------------------------------------------

/// Every well-formed `Q` denotes at least one well-formed `XR`.
pub proof fn lemma_denotes_inhabited(q: Q)
    requires
        q.wf(),
    ensures
        exists|v: XR| xr_wf(v) && #[trigger] denotes(q, v),
{
    match q {
        Q::Number(x) => {
            assert(xr_wf(XR::Fin(x.n(), x.d())));
            assert(denotes(q, XR::Fin(x.n(), x.d())));
        },
        Q::PosSat => {
            let v = XR::Fin(max_mag() + 1, 1);
            assert(xr_wf(v));
            assert(denotes(q, v));
        },
        Q::NegSat => {
            let v = XR::Fin(0 - (max_mag() + 1), 1);
            assert(xr_wf(v));
            assert(denotes(q, v));
        },
        Q::PosInf => {
            assert(denotes(q, XR::PosInfinity));
        },
        Q::NegInf => {
            assert(denotes(q, XR::NegInfinity));
        },
        Q::Nan => {
            assert(xr_wf(XR::Fin(0, 1)));
            assert(denotes(q, XR::Fin(0, 1)));
        },
    }
}

// ---------------------------------------------------------------------------
// N2 — the denotation of a `Number`, `PosInf` or `NegInf` is a singleton
// (up to `xr_eq`): naming the one witness makes later proofs about these
// three variants a substitution instead of a fresh case split.
// ---------------------------------------------------------------------------

/// A `Number(x)` denotes exactly `x`'s value, nothing else.
pub proof fn lemma_denotes_number_unique(x: Rat, v: XR)
    requires
        x.wf(),
        denotes(Q::Number(x), v),
    ensures
        xr_eq(v, XR::Fin(x.n(), x.d())),
{
}

/// `PosInf` denotes exactly `+∞`.
pub proof fn lemma_denotes_posinf_unique(v: XR)
    requires
        denotes(Q::PosInf, v),
    ensures
        v == XR::PosInfinity,
{
}

/// `NegInf` denotes exactly `-∞`.
pub proof fn lemma_denotes_neginf_unique(v: XR)
    requires
        denotes(Q::NegInf, v),
    ensures
        v == XR::NegInfinity,
{
}

// ---------------------------------------------------------------------------
// N3 — separation: a wf `Number`'s value can never fall in a saturation
// band. This is what makes `Number`, `PosSat` and `NegSat` denote disjoint
// sets of reals, which the necessity arguments in `laws_q.rs` need in order
// to rule out a `Number` (or the opposite-signed `Sat`) as an alternative,
// tighter answer to a cell that is actually `Nan`.
// ---------------------------------------------------------------------------

/// A representable rational's true value never lies in `PosSat`'s or
/// `NegSat`'s band: `wf` bounds `|n| <= max_mag() * d`, and both bands are
/// strict past it.
pub proof fn lemma_number_not_saturated(x: Rat)
    requires
        x.wf(),
    ensures
        !(x.n() > max_mag() * x.d()),
        !(x.n() < 0 - max_mag() * x.d()),
{
    assert(x.n() <= max_mag() * x.d()) by (nonlinear_arith)
        requires
            x.n() <= max_mag(),
            x.d() >= 1,
            max_mag() >= 0,
    ;
    assert(x.n() >= 0 - max_mag() * x.d()) by (nonlinear_arith)
        requires
            x.n() >= 0 - max_mag(),
            x.d() >= 1,
            max_mag() >= 0,
    ;
}

// ---------------------------------------------------------------------------
// Negation commutes with denotation — what makes `sub`'s containment (issue
// #28) a corollary of `add`'s rather than its own casework, since `Q::sub`
// is defined as `Q::add(a, b.neg())`.
// ---------------------------------------------------------------------------

/// `denotes` commutes with negation on both sides: `a` denotes `v` iff
/// `-a` denotes `-v`.
pub proof fn lemma_neg_denotes(a: Q, v: XR)
    requires
        a.wf(),
        xr_wf(v),
    ensures
        xr_wf(xr_neg(v)),
        denotes(a, v) == denotes(crate::ext::Q::spec_neg(a), xr_neg(v)),
{
    match a {
        Q::Number(x) => {
            match v {
                XR::Fin(n, d) => {
                    Rat::lemma_from_raw_spec_components((0 - x.n()) as i64, x.d() as i64);
                    assert((n * x.d() == x.n() * d) == ((0 - n) * x.d() == (0 - x.n()) * d)) by (
                        nonlinear_arith
                    );
                },
                _ => {},
            }
        },
        Q::PosSat | Q::NegSat | Q::PosInf | Q::NegInf | Q::Nan => {},
    }
}

} // verus!
