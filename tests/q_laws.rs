//! Issue #26: `Q`'s algebraic laws, and executable witnesses for exactly
//! where each one stops holding.
//!
//! `src/laws_q.rs` proves what holds: `add`/`mul` commutative
//! unconditionally, associativity/distributivity/monotonicity on the
//! all-`Number` exact path, `recip(x) == div(one, x)` unconditionally. This
//! file is the other half of that obligation — every law that does *not*
//! extend past its proven scope gets a concrete counterexample here, not
//! just a claim in a doc comment. Each one was checked by actually running
//! it before being written down.

use the_q::{MAX_MAG, Q, Rat};

/// `(a + b) + c != a + (b + c)` once a `Sat` appears: `a + b` saturates, and
/// `PosSat + Number(x)` is sound only for `x`'s matching sign — the
/// opposite sign carries no information, so it is `Nan`.
#[test]
fn add_associativity_fails_with_saturation() {
    let a = Q::Number(Rat::new(MAX_MAG, 1).unwrap());
    let b = Q::Number(Rat::new(MAX_MAG, 1).unwrap());
    let c = Q::Number(Rat::new(-MAX_MAG, 1).unwrap());

    let left = Q::add(Q::add(a, b), c);
    let right = Q::add(a, Q::add(b, c));

    assert_eq!(Q::add(a, b), Q::PosSat);
    assert_eq!(left, Q::Nan);
    assert_eq!(right, Q::Number(Rat::new(MAX_MAG, 1).unwrap()));
    assert_ne!(left, right);
}

/// `(a * b) * c != a * (b * c)` once a `Sat` appears: `a * b` saturates, and
/// multiplying it by a fraction inside `(0, 1)` reaches back into the
/// budget — sound only as `Nan` — while the other bracketing multiplies
/// first into a representable half and only then overflows.
#[test]
fn mul_associativity_fails_with_saturation() {
    let a = Q::Number(Rat::new(MAX_MAG, 1).unwrap());
    let b = Q::Number(Rat::new(MAX_MAG, 1).unwrap());
    let c = Q::Number(Rat::new(1, 2).unwrap());

    let left = Q::mul(Q::mul(a, b), c);
    let right = Q::mul(a, Q::mul(b, c));

    assert_eq!(Q::mul(a, b), Q::PosSat);
    assert_eq!(left, Q::Nan);
    assert_eq!(Q::mul(b, c), Q::Number(Rat::new(MAX_MAG, 2).unwrap()));
    assert_eq!(right, Q::PosSat);
    assert_ne!(left, right);
}

/// `a * (b + c) != a * b + a * c` once a `Sat` appears: `b + c` cancels
/// back to exactly `0` before `a` ever multiplies it, but distributed first,
/// `a * b` and `a * c` saturate to opposite-signed `Sat`s that carry no
/// information when added.
#[test]
fn distributive_fails_with_saturation() {
    let a = Q::Number(Rat::new(MAX_MAG, 1).unwrap());
    let b = Q::Number(Rat::new(MAX_MAG, 1).unwrap());
    let c = Q::Number(Rat::new(-MAX_MAG, 1).unwrap());

    let lhs = Q::mul(a, Q::add(b, c));
    let rhs = Q::add(Q::mul(a, b), Q::mul(a, c));

    assert_eq!(Q::add(b, c), Q::zero());
    assert_eq!(lhs, Q::zero());
    assert_eq!(Q::mul(a, b), Q::PosSat);
    assert_eq!(Q::mul(a, c), Q::NegSat);
    assert_eq!(rhs, Q::Nan);
    assert_ne!(lhs, rhs);
}

/// `Q` is not a semiring: it is commutative but not associative (nor
/// distributive) once saturation is reachable — see the three tests above.
/// `recip(x) == div(one, x)` holds unconditionally
/// (`theorem_q_recip_is_div_one`'s comment on `Q::recip`, `src/ext.rs`), but
/// `div(a, b) == mul(a, recip(b))` does not: `recip` throws away `b`'s
/// magnitude the instant it becomes `Nan`, which `div`'s own table does not
/// do for a saturated divisor.
#[test]
fn div_is_not_mul_by_recip_for_infinity_over_saturation() {
    let a = Q::PosInf;
    let b = Q::PosSat;

    assert_eq!(Q::div(a, b), Q::PosInf);
    assert_eq!(b.recip(), Q::Nan);
    assert_eq!(Q::mul(a, b.recip()), Q::Nan);
    assert_ne!(Q::div(a, b), Q::mul(a, b.recip()));
}

/// The sharpest of the six `div != mul . recip` cells: `0 / Sat` is exactly
/// `0` — the true quotient is `0` regardless of `Sat`'s actual value, so
/// `div` states it outright — but `recip(Sat)` alone is already `Nan` (its
/// image reaches back inside the budget), and `Nan` absorbs through the
/// following `mul` before `0`'s own information ever gets a say.
#[test]
fn div_is_not_mul_by_recip_for_zero_over_saturation() {
    let a = Q::zero();
    let b = Q::PosSat;

    assert_eq!(Q::div(a, b), Q::zero());
    assert_eq!(b.recip(), Q::Nan);
    assert_eq!(Q::mul(a, b.recip()), Q::Nan);
    assert_ne!(Q::div(a, b), Q::mul(a, b.recip()));
}
