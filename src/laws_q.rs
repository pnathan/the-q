//! Algebraic laws for [`Q`] (issue #26 §5/§10.3, the V6 gap this crate's laws
//! never closed at the `Q` level: `grep -n "Q::" src/laws.rs` was empty before
//! this file).
//!
//! Every claim below was checked empirically against the compiled crate
//! before it was attempted as a proof (random and exhaustive probing over the
//! 6-variant state space), so the scope here is not a guess:
//!
//! | law | scope |
//! |---|---|
//! | `add`, `mul` commutative | unconditional |
//! | associativity, distributivity | all-`Number`, exact path only |
//! | monotonicity | all-`Number`, exact path only — **fails even with both
//!   outputs `Number`, off the exact path**: `round_frac` is bounded-denominator
//!   rounding, not "nearest in a fixed set", so it is not a monotone map. See
//!   `tests/q_laws.rs` for the counterexample. |
//! | `recip(x) == div(one, x)` | unconditional — proven directly on
//!   [`crate::ext::Q::recip`]'s `ensures`, since that is its literal definition |
//!
//! Associativity and distributivity fail as soon as any operand is `PosSat`
//! or `NegSat` (concrete counterexamples in `tests/q_laws.rs`), and `mul`
//! additionally fails to associate on values that stay clear of `Sat`
//! entirely, because rounding a product to zero can manufacture a `0 · ∞`
//! indeterminate that exact multiplication never would. No associativity
//! defect bound is stated at this level: `Nan` and the unbounded `Sat`
//! intervals carry no metric to bound a defect against, unlike `Rat`'s
//! `theorem_add_associativity_bound`. `div(a, b) == mul(a, recip(b))` fails in
//! exactly the six cells `{NegInf, PosInf, Number(0)} × {PosSat, NegSat}`
//! (`tests/q_laws.rs`).

use verus_builtin_macros::verus;

#[allow(unused_imports)]
use verus_builtin::*;
#[allow(unused_imports)]
use vstd::prelude::*;

#[allow(unused_imports)]
use crate::ext::Q;
#[allow(unused_imports)]
use crate::model::*;
#[allow(unused_imports)]
use crate::q::*;
#[allow(unused_imports)]
use crate::round::*;
#[allow(unused_imports)]
use crate::types::{Dir, Rat};

verus! {

// ---------------------------------------------------------------------------
// The bridge lemma both associativity-exact theorems need: `Q::add_numbers`
// (etc.) takes their `Number` branch — i.e. `magnitude_fits` holds — whenever
// the stronger `exact_path` (I2 on the *reduced* pair) holds. Flagged by both
// consultations as the one genuinely nonlinear step in this file.
// ---------------------------------------------------------------------------

/// **`exact_path` implies `magnitude_fits`.** The reduced pair's budget bound
/// scales back up through the gcd: `|n| == |rn|·g <= max_mag()·g <=
/// max_mag()·(rd·g) == max_mag()·d`, using `rd >= 1`.
pub proof fn lemma_exact_path_implies_magnitude_fits(n: int, d: int)
    requires
        d > 0,
        exact_path(n, d),
    ensures
        magnitude_fits(n, d),
{
    if n == 0 {
        crate::model::lemma_max_mag_pow2();
        assert(magnitude_fits(n, d)) by (nonlinear_arith)
            requires
                n == 0,
                max_mag() > 0,
                d > 0,
        ;
    } else {
        let g = gcd_int(n, d);
        let rn = red_num(n, d);
        let rd = red_den(n, d);
        crate::round::lemma_reduce_exact(n, d);
        crate::round::lemma_reduce_abs(n, d);
        // `exact_path(n, d)` with `n != 0` unfolds to `fits_budget(rn, rd)`.
        assert(abs_int(rn) <= max_mag());
        assert(rd >= 1);
        assert(abs_int(rn) * g <= max_mag() * g) by (nonlinear_arith)
            requires
                abs_int(rn) <= max_mag(),
                g > 0,
        ;
        assert(max_mag() * g <= max_mag() * (rd * g)) by (nonlinear_arith)
            requires
                rd >= 1,
                g > 0,
                max_mag() >= 0,
        ;
        assert(abs_int(n) <= max_mag() * d) by (nonlinear_arith)
            requires
                abs_int(n) == abs_int(rn) * g,
                d == rd * g,
                abs_int(rn) * g <= max_mag() * g,
                max_mag() * g <= max_mag() * (rd * g),
        ;
    }
}

/// `prod_d(x, y) > 0`. Multiplication is uninterpreted outside a nonlinear
/// block (`VERIFICATION.md`, Verus note 4), so this one-line fact needs its
/// own lemma rather than following from `x.wf()`/`y.wf()` automatically —
/// every later call that hands `prod_d(x, y)` to something requiring `d > 0`
/// needs it in scope first.
pub proof fn lemma_prod_d_pos(x: Rat, y: Rat)
    requires
        x.wf(),
        y.wf(),
    ensures
        prod_d(x, y) > 0,
{
    assert(prod_d(x, y) == x.d() * y.d());
    assert(x.d() * y.d() > 0) by (nonlinear_arith)
        requires
            x.d() > 0,
            y.d() > 0,
    ;
}

// ---------------------------------------------------------------------------
// Commutativity: holds unconditionally, over the whole state space
// ---------------------------------------------------------------------------

/// **`Q::add` is commutative.** `add_n`/`mul_n` reorder for free (same two
/// summands); `prod_d` needs multiplication commutativity. Every other cell
/// of the table is already written symmetrically (`(Number, PosSat)` and
/// `(PosSat, Number)` call the same helper with the same arguments).
pub proof fn theorem_q_add_commutative(a: Q, b: Q)
    requires
        a.wf(),
        b.wf(),
    ensures
        Q::spec_add(a, b) == Q::spec_add(b, a),
{
    match (a, b) {
        (Q::Number(x), Q::Number(y)) => {
            assert(add_n(x, y) == add_n(y, x));
            assert(prod_d(x, y) == prod_d(y, x)) by (nonlinear_arith);
        },
        _ => {},
    }
}

/// **`Q::mul` is commutative.** See [`theorem_q_add_commutative`]; here both
/// `mul_n` and `prod_d` need multiplication commutativity.
pub proof fn theorem_q_mul_commutative(a: Q, b: Q)
    requires
        a.wf(),
        b.wf(),
    ensures
        Q::spec_mul(a, b) == Q::spec_mul(b, a),
{
    match (a, b) {
        (Q::Number(x), Q::Number(y)) => {
            assert(mul_n(x, y) == mul_n(y, x)) by (nonlinear_arith);
            assert(prod_d(x, y) == prod_d(y, x)) by (nonlinear_arith);
        },
        _ => {},
    }
}

// ---------------------------------------------------------------------------
// Associativity and distributivity: all-`Number`, exact path only
// ---------------------------------------------------------------------------

/// **`Q::add` is associative on the all-`Number` exact path.** A thin wrapper:
/// [`lemma_exact_path_implies_magnitude_fits`] forces `add_numbers` into its
/// `Number` branch, [`crate::laws::theorem_exact_path_is_exact`] identifies
/// that branch's value with the exact sum, and
/// [`crate::laws::theorem_add_associative_exact`] does the real work.
pub proof fn theorem_q_add_associative_exact(a: Rat, b: Rat, c: Rat)
    requires
        a.wf(),
        b.wf(),
        c.wf(),
        exact_path(add_n(a, b), prod_d(a, b)),
        exact_path(add_n(b, c), prod_d(b, c)),
        ({
            let ab = round_frac(add_n(a, b), prod_d(a, b), Dir::Nearest);
            let bc = round_frac(add_n(b, c), prod_d(b, c), Dir::Nearest);
            &&& exact_path(add_n(ab, c), prod_d(ab, c))
            &&& exact_path(add_n(a, bc), prod_d(a, bc))
        }),
    ensures
        ({
            let ab = round_frac(add_n(a, b), prod_d(a, b), Dir::Nearest);
            let bc = round_frac(add_n(b, c), prod_d(b, c), Dir::Nearest);
            Q::spec_add(Q::spec_add(Q::Number(a), Q::Number(b)), Q::Number(c)) == Q::spec_add(
                Q::Number(a),
                Q::spec_add(Q::Number(b), Q::Number(c)),
            )
        }),
{
    crate::laws::theorem_add_associative_exact(a, b, c, Dir::Nearest);
    lemma_prod_d_pos(a, b);
    lemma_prod_d_pos(b, c);
    lemma_exact_path_implies_magnitude_fits(add_n(a, b), prod_d(a, b));
    lemma_exact_path_implies_magnitude_fits(add_n(b, c), prod_d(b, c));
    let ab = round_frac(add_n(a, b), prod_d(a, b), Dir::Nearest);
    let bc = round_frac(add_n(b, c), prod_d(b, c), Dir::Nearest);
    crate::round::lemma_round_frac_wf(add_n(a, b), prod_d(a, b), Dir::Nearest);
    crate::round::lemma_round_frac_wf(add_n(b, c), prod_d(b, c), Dir::Nearest);
    lemma_prod_d_pos(ab, c);
    lemma_prod_d_pos(a, bc);
    lemma_exact_path_implies_magnitude_fits(add_n(ab, c), prod_d(ab, c));
    lemma_exact_path_implies_magnitude_fits(add_n(a, bc), prod_d(a, bc));
    let left = round_frac(add_n(ab, c), prod_d(ab, c), Dir::Nearest);
    let right = round_frac(add_n(a, bc), prod_d(a, bc), Dir::Nearest);
    crate::round::lemma_round_frac_wf(add_n(ab, c), prod_d(ab, c), Dir::Nearest);
    crate::round::lemma_round_frac_wf(add_n(a, bc), prod_d(a, bc), Dir::Nearest);
    crate::laws::lemma_canonical_eq(left, right);
}

/// **`Q::mul` is associative on the all-`Number` exact path.** See
/// [`theorem_q_add_associative_exact`].
pub proof fn theorem_q_mul_associative_exact(a: Rat, b: Rat, c: Rat)
    requires
        a.wf(),
        b.wf(),
        c.wf(),
        exact_path(mul_n(a, b), prod_d(a, b)),
        exact_path(mul_n(b, c), prod_d(b, c)),
        ({
            let ab = round_frac(mul_n(a, b), prod_d(a, b), Dir::Nearest);
            let bc = round_frac(mul_n(b, c), prod_d(b, c), Dir::Nearest);
            &&& exact_path(mul_n(ab, c), prod_d(ab, c))
            &&& exact_path(mul_n(a, bc), prod_d(a, bc))
        }),
    ensures
        ({
            let ab = round_frac(mul_n(a, b), prod_d(a, b), Dir::Nearest);
            let bc = round_frac(mul_n(b, c), prod_d(b, c), Dir::Nearest);
            Q::spec_mul(Q::spec_mul(Q::Number(a), Q::Number(b)), Q::Number(c)) == Q::spec_mul(
                Q::Number(a),
                Q::spec_mul(Q::Number(b), Q::Number(c)),
            )
        }),
{
    lemma_prod_d_pos(a, b);
    lemma_prod_d_pos(b, c);
    lemma_exact_path_implies_magnitude_fits(mul_n(a, b), prod_d(a, b));
    lemma_exact_path_implies_magnitude_fits(mul_n(b, c), prod_d(b, c));
    let ab = round_frac(mul_n(a, b), prod_d(a, b), Dir::Nearest);
    let bc = round_frac(mul_n(b, c), prod_d(b, c), Dir::Nearest);
    crate::round::lemma_round_frac_wf(mul_n(a, b), prod_d(a, b), Dir::Nearest);
    crate::round::lemma_round_frac_wf(mul_n(b, c), prod_d(b, c), Dir::Nearest);
    lemma_prod_d_pos(ab, c);
    lemma_prod_d_pos(a, bc);
    lemma_exact_path_implies_magnitude_fits(mul_n(ab, c), prod_d(ab, c));
    lemma_exact_path_implies_magnitude_fits(mul_n(a, bc), prod_d(a, bc));
    let left = round_frac(mul_n(ab, c), prod_d(ab, c), Dir::Nearest);
    let right = round_frac(mul_n(a, bc), prod_d(a, bc), Dir::Nearest);
    crate::round::lemma_round_frac_wf(mul_n(ab, c), prod_d(ab, c), Dir::Nearest);
    crate::round::lemma_round_frac_wf(mul_n(a, bc), prod_d(a, bc), Dir::Nearest);
    crate::laws::theorem_exact_path_is_exact(mul_n(a, b), prod_d(a, b), Dir::Nearest);
    crate::laws::theorem_exact_path_is_exact(mul_n(b, c), prod_d(b, c), Dir::Nearest);
    crate::laws::theorem_exact_path_is_exact(mul_n(ab, c), prod_d(ab, c), Dir::Nearest);
    crate::laws::theorem_exact_path_is_exact(mul_n(a, bc), prod_d(a, bc), Dir::Nearest);
    crate::laws::theorem_mul_associative_exact(a, b, c, ab, bc, left, right);
    crate::laws::lemma_canonical_eq(left, right);
}

/// **`Q::mul` distributes over `Q::add` on the all-`Number` exact path.**
pub proof fn theorem_q_distributive_exact(a: Rat, b: Rat, c: Rat)
    requires
        a.wf(),
        b.wf(),
        c.wf(),
        exact_path(add_n(b, c), prod_d(b, c)),
        ({
            let bc = round_frac(add_n(b, c), prod_d(b, c), Dir::Nearest);
            &&& exact_path(mul_n(a, bc), prod_d(a, bc))
        }),
        exact_path(mul_n(a, b), prod_d(a, b)),
        exact_path(mul_n(a, c), prod_d(a, c)),
        ({
            let ab = round_frac(mul_n(a, b), prod_d(a, b), Dir::Nearest);
            let ac = round_frac(mul_n(a, c), prod_d(a, c), Dir::Nearest);
            &&& exact_path(add_n(ab, ac), prod_d(ab, ac))
        }),
    ensures
        ({
            let bc = round_frac(add_n(b, c), prod_d(b, c), Dir::Nearest);
            let ab = round_frac(mul_n(a, b), prod_d(a, b), Dir::Nearest);
            let ac = round_frac(mul_n(a, c), prod_d(a, c), Dir::Nearest);
            Q::spec_mul(Q::Number(a), Q::spec_add(Q::Number(b), Q::Number(c))) == Q::spec_add(
                Q::spec_mul(Q::Number(a), Q::Number(b)),
                Q::spec_mul(Q::Number(a), Q::Number(c)),
            )
        }),
{
    lemma_prod_d_pos(b, c);
    lemma_exact_path_implies_magnitude_fits(add_n(b, c), prod_d(b, c));
    let bc = round_frac(add_n(b, c), prod_d(b, c), Dir::Nearest);
    crate::round::lemma_round_frac_wf(add_n(b, c), prod_d(b, c), Dir::Nearest);
    lemma_prod_d_pos(a, bc);
    lemma_prod_d_pos(a, b);
    lemma_prod_d_pos(a, c);
    lemma_exact_path_implies_magnitude_fits(mul_n(a, bc), prod_d(a, bc));
    lemma_exact_path_implies_magnitude_fits(mul_n(a, b), prod_d(a, b));
    lemma_exact_path_implies_magnitude_fits(mul_n(a, c), prod_d(a, c));
    let ab = round_frac(mul_n(a, b), prod_d(a, b), Dir::Nearest);
    let ac = round_frac(mul_n(a, c), prod_d(a, c), Dir::Nearest);
    crate::round::lemma_round_frac_wf(mul_n(a, b), prod_d(a, b), Dir::Nearest);
    crate::round::lemma_round_frac_wf(mul_n(a, c), prod_d(a, c), Dir::Nearest);
    lemma_prod_d_pos(ab, ac);
    lemma_exact_path_implies_magnitude_fits(add_n(ab, ac), prod_d(ab, ac));
    let lhs = round_frac(mul_n(a, bc), prod_d(a, bc), Dir::Nearest);
    let rhs = round_frac(add_n(ab, ac), prod_d(ab, ac), Dir::Nearest);
    crate::round::lemma_round_frac_wf(mul_n(a, bc), prod_d(a, bc), Dir::Nearest);
    crate::round::lemma_round_frac_wf(add_n(ab, ac), prod_d(ab, ac), Dir::Nearest);
    crate::laws::theorem_exact_path_is_exact(add_n(b, c), prod_d(b, c), Dir::Nearest);
    crate::laws::theorem_exact_path_is_exact(mul_n(a, bc), prod_d(a, bc), Dir::Nearest);
    crate::laws::theorem_exact_path_is_exact(mul_n(a, b), prod_d(a, b), Dir::Nearest);
    crate::laws::theorem_exact_path_is_exact(mul_n(a, c), prod_d(a, c), Dir::Nearest);
    crate::laws::theorem_exact_path_is_exact(add_n(ab, ac), prod_d(ab, ac), Dir::Nearest);
    crate::laws::theorem_distributive_exact(a, b, c, bc, lhs, ab, ac, rhs);
    crate::laws::lemma_canonical_eq(lhs, rhs);
}

// ---------------------------------------------------------------------------
// Monotonicity: all-`Number`, exact path only. This is the sharpest of the
// four scopes: monotonicity fails even when *both* outputs are `Number`, off
// the exact path (`tests/q_laws.rs` has the counterexample) — `round_frac` is
// bounded-denominator rounding, not "nearest point in a fixed grid", so it is
// not a monotone map in general.
// ---------------------------------------------------------------------------

/// **`Q::add` is monotone in its left argument on the all-`Number` exact
/// path.** `theorem_add_monotone_exact` gives the inequality on the exact
/// numerator/denominator pairs; [`crate::interval::lemma_frac_chain_le`]
/// transports it across the two `q_is` identifications onto the rounded
/// (here, exact) results.
pub proof fn theorem_q_add_monotone_exact(a: Rat, b: Rat, c: Rat)
    requires
        a.wf(),
        b.wf(),
        c.wf(),
        q_le(a, b),
        exact_path(add_n(a, c), prod_d(a, c)),
        exact_path(add_n(b, c), prod_d(b, c)),
    ensures
        ({
            let ac = round_frac(add_n(a, c), prod_d(a, c), Dir::Nearest);
            let bc = round_frac(add_n(b, c), prod_d(b, c), Dir::Nearest);
            &&& Q::spec_add(Q::Number(a), Q::Number(c)) == Q::Number(ac)
            &&& Q::spec_add(Q::Number(b), Q::Number(c)) == Q::Number(bc)
            &&& q_le(ac, bc)
        }),
{
    lemma_prod_d_pos(a, c);
    lemma_prod_d_pos(b, c);
    lemma_exact_path_implies_magnitude_fits(add_n(a, c), prod_d(a, c));
    lemma_exact_path_implies_magnitude_fits(add_n(b, c), prod_d(b, c));
    crate::laws::theorem_add_monotone_exact(a, b, c);
    let ac = round_frac(add_n(a, c), prod_d(a, c), Dir::Nearest);
    let bc = round_frac(add_n(b, c), prod_d(b, c), Dir::Nearest);
    crate::laws::theorem_exact_path_is_exact(add_n(a, c), prod_d(a, c), Dir::Nearest);
    crate::laws::theorem_exact_path_is_exact(add_n(b, c), prod_d(b, c), Dir::Nearest);
    crate::interval::lemma_frac_chain_le(
        ac.n(),
        ac.d(),
        add_n(a, c),
        prod_d(a, c),
        add_n(b, c),
        prod_d(b, c),
        bc.n(),
        bc.d(),
    );
}

} // verus!
