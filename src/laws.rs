//! Algebraic laws (obligation V6).
//!
//! # What holds, and what does not
//!
//! | law | status |
//! |---|---|
//! | `a + b == b + a`, `a * b == b * a` | **always**, bit-for-bit |
//! | `(a + b) + c == a + (b + c)` | exact path: **exactly**; otherwise: **within `4 · 2^-61 · m`** |
//! | `(a * b) * c == a * (b * c)` | exact path: **exactly**; otherwise, on `[0, 1]`: **within `6 · 2^-61`** |
//! | `a * (b + c) == a*b + a*c` | **only on the exact path** |
//! | `Ord` is a total order agreeing with the ghost order | always |
//! | `-(-a) == a`, `abs(abs(a)) == abs(a)`, `1/(1/a) == a` | always |
//!
//! Commutativity survives rounding. Both orderings feed *provably equal*
//! integers into the same rounding function. Associativity does not survive
//! rounding. Rounding the inner sum first can land on a different grid point
//! than rounding the outer one. That failure is bounded.
//! `theorem_add_associativity_bound` and
//! `theorem_mul_associativity_bound_unit_interval` below state associativity up
//! to a proven error. The consuming engine's order-independence claims
//! therefore hold **exactly** whenever the whole computation stays inside the
//! budget, and **up to that proven error bound** otherwise. See `README.md`.

use verus_builtin_macros::verus;

#[allow(unused_imports)]
use verus_builtin::*;
#[allow(unused_imports)]
use vstd::prelude::*;

#[allow(unused_imports)]
use crate::gcd::*;
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
// Canonicality: structural equality is mathematical equality
// ---------------------------------------------------------------------------

/// Euclid's lemma: if `gcd(a, b) == 1` and `a | b·c` then `a | c`.
///
/// Derived from `gcd(a·c, b·c) == c · gcd(a, b) == c`: `a` divides both `a·c`
/// and `b·c`, hence divides their gcd.
pub proof fn lemma_euclid(a: nat, b: nat, c: nat)
    requires
        a > 0,
        gcd_nat(a, b) == 1,
        divides(a as int, (b * c) as int),
    ensures
        divides(a as int, c as int),
{
    if c == 0 {
        crate::model::lemma_divides_basic(a as int);
    } else {
        lemma_gcd_scale(c, a, b);
        // gcd(c*a, c*b) == c * gcd(a,b) == c
        assert(gcd_nat((c * a) as nat, (c * b) as nat) == c);
        crate::model::lemma_divides_basic(a as int);
        assert(divides(a as int, (c * a) as int)) by {
            assert((c * a) as int == (a as int) * (c as int)) by (nonlinear_arith);
        }
        assert(divides(a as int, (c * b) as int)) by {
            assert((c * b) as int == (b * c) as int) by (nonlinear_arith);
        }
        lemma_gcd_greatest((c * a) as nat, (c * b) as nat, a as int);
    }
}

/// **Canonicality.** Two well-formed `Rat` are mathematically equal exactly when
/// they are structurally equal.
///
/// This property makes `PartialEq`, `Eq` and `Hash` safe to derive. It also
/// gives every value exactly one bit pattern. Comparison and hashing are thus
/// deterministic.
pub proof fn lemma_canonical_eq(a: Rat, b: Rat)
    requires
        a.wf(),
        b.wf(),
    ensures
        q_eq(a, b) <==> a == b,
{
    if q_eq(a, b) {
        // a.num * b.den == b.num * a.den, with both fractions in lowest terms.
        // a.den divides b.num * a.den, hence divides a.num * b.den; a.den is
        // coprime to a.num, so a.den | b.den. Symmetrically b.den | a.den.
        // `wf` gives gcd(|num|, den) == 1. Euclid's lemma takes the divisor
        // first, so `lemma_gcd_sym` flips both.
        crate::q::lemma_gcd_sym(abs_int(a.n()) as nat, a.d() as nat);
        crate::q::lemma_gcd_sym(abs_int(b.n()) as nat, b.d() as nat);
        assert(divides(a.d(), a.n() * b.d())) by {
            assert(a.n() * b.d() == b.n() * a.d());
            assert(b.n() * a.d() == a.d() * b.n()) by (nonlinear_arith);
            assert(b.n() * a.d() == a.d() * b.n());
        }
        // `lemma_euclid` takes `nat`s, so the divisibility has to be carried
        // across the sign: `d | n·b.d` gives `d | |n|·b.d` because divisibility
        // is closed under negation.
        assert(divides(a.d(), abs_int(a.n()) * b.d())) by {
            let ka = choose|k: int| a.n() * b.d() == #[trigger] (a.d() * k);
            if a.n() < 0 {
                assert(abs_int(a.n()) * b.d() == a.d() * (-ka)) by (nonlinear_arith)
                    requires
                        a.n() * b.d() == a.d() * ka,
                        abs_int(a.n()) == -a.n(),
                ;
            }
        }
        lemma_euclid(a.d() as nat, abs_int(a.n()) as nat, b.d() as nat);
        assert(divides(b.d(), b.n() * a.d())) by {
            assert(b.n() * a.d() == a.n() * b.d());
            assert(a.n() * b.d() == b.d() * a.n()) by (nonlinear_arith);
            assert(a.n() * b.d() == b.d() * a.n());
        }
        assert(divides(b.d(), abs_int(b.n()) * a.d())) by {
            let kb = choose|k: int| b.n() * a.d() == #[trigger] (b.d() * k);
            if b.n() < 0 {
                assert(abs_int(b.n()) * a.d() == b.d() * (-kb)) by (nonlinear_arith)
                    requires
                        b.n() * a.d() == b.d() * kb,
                        abs_int(b.n()) == -b.n(),
                ;
            }
        }
        lemma_euclid(b.d() as nat, abs_int(b.n()) as nat, a.d() as nat);
        lemma_divides_le(a.d(), b.d());
        lemma_divides_le(b.d(), a.d());
        assert(a.d() == b.d());
        assert(a.n() == b.n()) by (nonlinear_arith)
            requires
                a.d() == b.d(),
                a.d() > 0,
                a.n() * b.d() == b.n() * a.d(),
        ;
    }
}

// ---------------------------------------------------------------------------
// Commutativity: holds unconditionally, rounding included
// ---------------------------------------------------------------------------

/// **`add` is commutative**, bit-for-bit, rounding included.
///
/// `add_n(a, b)` and `add_n(b, a)` are equal integers and `prod_d` is
/// symmetric, so both calls apply [`round_frac`] to the same arguments.
pub proof fn theorem_add_commutative(a: Rat, b: Rat, dir: Dir)
    requires
        a.wf(),
        b.wf(),
    ensures
        round_frac(add_n(a, b), prod_d(a, b), dir) == round_frac(add_n(b, a), prod_d(b, a), dir),
{
    assert(add_n(a, b) == add_n(b, a));
    assert(prod_d(a, b) == prod_d(b, a)) by (nonlinear_arith);
}

/// **`mul` is commutative**, bit-for-bit, rounding included.
pub proof fn theorem_mul_commutative(a: Rat, b: Rat, dir: Dir)
    requires
        a.wf(),
        b.wf(),
    ensures
        round_frac(mul_n(a, b), prod_d(a, b), dir) == round_frac(mul_n(b, a), prod_d(b, a), dir),
{
    assert(mul_n(a, b) == mul_n(b, a)) by (nonlinear_arith);
    assert(prod_d(a, b) == prod_d(b, a)) by (nonlinear_arith);
}

// ---------------------------------------------------------------------------
// The exactness theorem, and associativity/distributivity on the exact path
// ---------------------------------------------------------------------------

/// **The exactness theorem (R1, lifted).** If every exact intermediate of a
/// computation fits the budget, the computation is end-to-end exact. The result
/// is not merely accurate to within a bound. It is *exact*.
///
/// Stated here for a single operation; [`crate::nary::theorem_exact_fold_is_exact`]
/// lifts it to folds, and composing the two covers any expression tree.
pub proof fn theorem_exact_path_is_exact(n: int, d: int, dir: Dir)
    requires
        d > 0,
        exact_path(n, d),
    ensures
        q_is(round_frac(n, d, dir), n, d),
        round_frac(n, d, dir).wf(),
{
    crate::round::lemma_r1_identity(n, d, dir);
}

/// **`add` is associative on the exact path.**
pub proof fn theorem_add_associative_exact(a: Rat, b: Rat, c: Rat, dir: Dir)
    requires
        a.wf(),
        b.wf(),
        c.wf(),
        exact_path(add_n(a, b), prod_d(a, b)),
        exact_path(add_n(b, c), prod_d(b, c)),
        ({
            let ab = round_frac(add_n(a, b), prod_d(a, b), dir);
            let bc = round_frac(add_n(b, c), prod_d(b, c), dir);
            &&& exact_path(add_n(ab, c), prod_d(ab, c))
            &&& exact_path(add_n(a, bc), prod_d(a, bc))
        }),
    ensures
        ({
            let ab = round_frac(add_n(a, b), prod_d(a, b), dir);
            let bc = round_frac(add_n(b, c), prod_d(b, c), dir);
            let left = round_frac(add_n(ab, c), prod_d(ab, c), dir);
            let right = round_frac(add_n(a, bc), prod_d(a, bc), dir);
            q_eq(left, right)
        }),
{
    crate::q::lemma_op_widths(a, b);
    crate::q::lemma_op_widths(b, c);
    let ab = round_frac(add_n(a, b), prod_d(a, b), dir);
    let bc = round_frac(add_n(b, c), prod_d(b, c), dir);
    crate::round::lemma_round_frac_wf(add_n(a, b), prod_d(a, b), dir);
    crate::round::lemma_round_frac_wf(add_n(b, c), prod_d(b, c), dir);
    theorem_exact_path_is_exact(add_n(a, b), prod_d(a, b), dir);
    theorem_exact_path_is_exact(add_n(b, c), prod_d(b, c), dir);
    crate::q::lemma_op_widths(ab, c);
    crate::q::lemma_op_widths(a, bc);
    let left = round_frac(add_n(ab, c), prod_d(ab, c), dir);
    let right = round_frac(add_n(a, bc), prod_d(a, bc), dir);
    crate::round::lemma_round_frac_wf(add_n(ab, c), prod_d(ab, c), dir);
    crate::round::lemma_round_frac_wf(add_n(a, bc), prod_d(a, bc), dir);
    theorem_exact_path_is_exact(add_n(ab, c), prod_d(ab, c), dir);
    theorem_exact_path_is_exact(add_n(a, bc), prod_d(a, bc), dir);
    // Both equal (a + b + c) exactly, and exact equality of values is q_eq.
    lemma_add_assoc_exact_values(a, b, c, ab, bc, left, right);
}

/// Cancel a positive common factor from both sides of an equation.
pub proof fn lemma_cancel_pos(x: int, y: int, c: int)
    requires
        c > 0,
        x * c == y * c,
    ensures
        x == y,
{
    assert(x == y) by (nonlinear_arith)
        requires
            c > 0,
            x * c == y * c,
    ;
}

/// Two `Rat` denoting the same fraction are equal as values.
pub proof fn lemma_same_value_eq(x: Rat, y: Rat, n: int, d: int)
    requires
        d > 0,
        x.d() > 0,
        y.d() > 0,
        q_is(x, n, d),
        q_is(y, n, d),
    ensures
        q_eq(x, y),
{
    // (x.n·y.d)·d == n·x.d·y.d == (y.n·x.d)·d, then cancel the positive d.
    assert((x.n() * y.d()) * d == (x.n() * d) * y.d()) by (nonlinear_arith);
    assert((y.n() * x.d()) * d == (y.n() * d) * x.d()) by (nonlinear_arith);
    assert((x.n() * d) * y.d() == (n * x.d()) * y.d());
    assert((y.n() * d) * x.d() == (n * y.d()) * x.d());
    assert((n * x.d()) * y.d() == (n * y.d()) * x.d()) by (nonlinear_arith);
    lemma_cancel_pos(x.n() * y.d(), y.n() * x.d(), d);
}

/// The left bracketing of `a + b + c`, on the exact path, denotes the common
/// sum `((a.n·b.d + b.n·a.d)·c.d + c.n·a.d·b.d) / (a.d·b.d·c.d)`.
///
/// Take the outer step's cross-multiplication, scale it by `a.d·b.d`,
/// substitute the inner step, and cancel the positive `ab.d`.
///
/// Two rules make this proof go through. First, a `by (nonlinear_arith)` block
/// sees only the facts in its own `requires` clause. It does not inherit the
/// surrounding context. Thus each step that combines earlier facts is a plain
/// `assert`, and only pure ring identities go to the nonlinear tactic. Second,
/// named subterms keep those identities small. A goal with five variables and
/// degree five exhausts the solver budget.
pub proof fn lemma_left_assoc_value(a: Rat, b: Rat, c: Rat, ab: Rat, left: Rat, sn: int, sd: int)
    requires
        a.wf(),
        b.wf(),
        c.wf(),
        ab.wf(),
        left.wf(),
        q_is(ab, add_n(a, b), prod_d(a, b)),
        q_is(left, add_n(ab, c), prod_d(ab, c)),
        sn == (a.n() * b.d() + b.n() * a.d()) * c.d() + c.n() * (a.d() * b.d()),
        sd == (a.d() * b.d()) * c.d(),
    ensures
        q_is(left, sn, sd),
{
    let ad = a.d();
    let bd = b.d();
    let cd = c.d();
    let ld = left.d();
    let nab = a.n() * bd + b.n() * ad;
    let x = nab * cd;
    let y = c.n() * (ad * bd);
    // Scale the outer relation by ad·bd. Plain assert: linear in the hypothesis.
    assert((left.n() * (ab.d() * cd)) * (ad * bd) == ((ab.n() * cd + c.n() * ab.d()) * ld) * (ad
        * bd));
    // Left side regroups to ab.d · (left.n · sd). Pure identity.
    assert((left.n() * (ab.d() * cd)) * (ad * bd) == ab.d() * (left.n() * ((ad * bd) * cd)))
        by (nonlinear_arith);
    assert(left.n() * ((ad * bd) * cd) == left.n() * sd);
    // Right side: distribute, then rearrange each half. Pure identities.
    assert(((ab.n() * cd + c.n() * ab.d()) * ld) * (ad * bd) == ((ab.n() * cd) * ld) * (ad * bd)
        + ((c.n() * ab.d()) * ld) * (ad * bd)) by (nonlinear_arith);
    assert(((ab.n() * cd) * ld) * (ad * bd) == (ab.n() * (ad * bd)) * (cd * ld))
        by (nonlinear_arith);
    assert(((c.n() * ab.d()) * ld) * (ad * bd) == ab.d() * (y * ld)) by (nonlinear_arith)
        requires
            y == c.n() * (ad * bd),
    ;
    // Substitute the inner step. Plain assert.
    assert(ab.n() * (ad * bd) == nab * ab.d());
    assert((ab.n() * (ad * bd)) * (cd * ld) == (nab * ab.d()) * (cd * ld));
    assert((nab * ab.d()) * (cd * ld) == ab.d() * (x * ld)) by (nonlinear_arith)
        requires
            x == nab * cd,
    ;
    // Recombine. Small identity in named subterms.
    assert(ab.d() * (x * ld) + ab.d() * (y * ld) == ab.d() * ((x + y) * ld)) by (nonlinear_arith);
    assert(x + y == sn);
    assert(ab.d() * (left.n() * sd) == ab.d() * (sn * ld));
    assert((left.n() * sd) * ab.d() == (sn * ld) * ab.d()) by (nonlinear_arith)
        requires
            ab.d() * (left.n() * sd) == ab.d() * (sn * ld),
    ;
    lemma_cancel_pos(left.n() * sd, sn * ld, ab.d());
}

/// The right bracketing of `a + b + c` denotes the same common sum.
///
/// The explicit `rlimit` raises the solver budget for this identity. The
/// identity is at the edge of the default budget. The sibling lemmas carry the
/// same note about the rlimit.
#[verifier::rlimit(20)]
pub proof fn lemma_right_assoc_value(a: Rat, b: Rat, c: Rat, bc: Rat, right: Rat, sn: int, sd: int)
    requires
        a.wf(),
        b.wf(),
        c.wf(),
        bc.wf(),
        right.wf(),
        q_is(bc, add_n(b, c), prod_d(b, c)),
        q_is(right, add_n(a, bc), prod_d(a, bc)),
        sn == (a.n() * b.d() + b.n() * a.d()) * c.d() + c.n() * (a.d() * b.d()),
        sd == (a.d() * b.d()) * c.d(),
    ensures
        q_is(right, sn, sd),
{
    let ad = a.d();
    let bd = b.d();
    let cd = c.d();
    let rd = right.d();
    let nbc = b.n() * cd + c.n() * bd;
    let x = a.n() * (bd * cd);
    let y = nbc * ad;
    assert((right.n() * (ad * bc.d())) * (bd * cd) == ((a.n() * bc.d() + bc.n() * ad) * rd) * (bd
        * cd));
    assert((right.n() * (ad * bc.d())) * (bd * cd) == bc.d() * (right.n() * ((ad * bd) * cd)))
        by (nonlinear_arith);
    assert(right.n() * ((ad * bd) * cd) == right.n() * sd);
    assert(((a.n() * bc.d() + bc.n() * ad) * rd) * (bd * cd) == ((a.n() * bc.d()) * rd) * (bd * cd)
        + ((bc.n() * ad) * rd) * (bd * cd)) by (nonlinear_arith);
    assert(((a.n() * bc.d()) * rd) * (bd * cd) == bc.d() * (x * rd)) by (nonlinear_arith)
        requires
            x == a.n() * (bd * cd),
    ;
    assert(((bc.n() * ad) * rd) * (bd * cd) == (bc.n() * (bd * cd)) * (ad * rd))
        by (nonlinear_arith);
    assert(bc.n() * (bd * cd) == nbc * bc.d());
    assert((bc.n() * (bd * cd)) * (ad * rd) == (nbc * bc.d()) * (ad * rd));
    assert((nbc * bc.d()) * (ad * rd) == bc.d() * (y * rd)) by (nonlinear_arith)
        requires
            y == nbc * ad,
    ;
    assert(bc.d() * (x * rd) + bc.d() * (y * rd) == bc.d() * ((x + y) * rd)) by (nonlinear_arith);
    // The two numerators agree by ring.
    assert(x + y == sn) by (nonlinear_arith)
        requires
            x == a.n() * (bd * cd),
            y == (b.n() * cd + c.n() * bd) * ad,
            sn == (a.n() * bd + b.n() * ad) * cd + c.n() * (ad * bd),
    ;
    assert(bc.d() * (right.n() * sd) == bc.d() * (sn * rd));
    assert((right.n() * sd) * bc.d() == (sn * rd) * bc.d()) by (nonlinear_arith)
        requires
            bc.d() * (right.n() * sd) == bc.d() * (sn * rd),
    ;
    lemma_cancel_pos(right.n() * sd, sn * rd, bc.d());
}

/// The pure-rational core of associativity: with every step exact, both
/// bracketings denote the same rational.
pub proof fn lemma_add_assoc_exact_values(a: Rat, b: Rat, c: Rat, ab: Rat, bc: Rat, left: Rat, right: Rat)
    requires
        a.wf(),
        b.wf(),
        c.wf(),
        ab.wf(),
        bc.wf(),
        left.wf(),
        right.wf(),
        q_is(ab, add_n(a, b), prod_d(a, b)),
        q_is(bc, add_n(b, c), prod_d(b, c)),
        q_is(left, add_n(ab, c), prod_d(ab, c)),
        q_is(right, add_n(a, bc), prod_d(a, bc)),
    ensures
        q_eq(left, right),
{
    let sn = (a.n() * b.d() + b.n() * a.d()) * c.d() + c.n() * (a.d() * b.d());
    let sd = (a.d() * b.d()) * c.d();
    assert(sd > 0) by (nonlinear_arith)
        requires
            sd == (a.d() * b.d()) * c.d(),
            a.d() > 0,
            b.d() > 0,
            c.d() > 0,
    ;
    lemma_left_assoc_value(a, b, c, ab, left, sn, sd);
    lemma_right_assoc_value(a, b, c, bc, right, sn, sd);
    lemma_same_value_eq(left, right, sn, sd);
}

/// **`mul` is associative on the exact path.**
///
/// Same shape as the additive case: scale the outer relation by the inner
/// denominators, substitute, cancel.
pub proof fn theorem_mul_associative_exact(a: Rat, b: Rat, c: Rat, ab: Rat, bc: Rat, left: Rat, right: Rat)
    requires
        a.wf(),
        b.wf(),
        c.wf(),
        ab.wf(),
        bc.wf(),
        left.wf(),
        right.wf(),
        q_is(ab, mul_n(a, b), prod_d(a, b)),
        q_is(bc, mul_n(b, c), prod_d(b, c)),
        q_is(left, mul_n(ab, c), prod_d(ab, c)),
        q_is(right, mul_n(a, bc), prod_d(a, bc)),
    ensures
        q_eq(left, right),
{
    let pn = (a.n() * b.n()) * c.n();
    let pd = (a.d() * b.d()) * c.d();
    assert(pd > 0) by (nonlinear_arith)
        requires
            pd == (a.d() * b.d()) * c.d(),
            a.d() > 0,
            b.d() > 0,
            c.d() > 0,
    ;
    lemma_mul_chain_value(a, b, c, ab, left, pn, pd);
    lemma_mul_chain_value_right(a, b, c, bc, right, pn, pd);
    lemma_same_value_eq(left, right, pn, pd);
}

/// `(a·b)·c` denotes `(a.n·b.n·c.n) / (a.d·b.d·c.d)`.
pub proof fn lemma_mul_chain_value(a: Rat, b: Rat, c: Rat, ab: Rat, left: Rat, pn: int, pd: int)
    requires
        a.wf(),
        b.wf(),
        c.wf(),
        ab.wf(),
        left.wf(),
        q_is(ab, mul_n(a, b), prod_d(a, b)),
        q_is(left, mul_n(ab, c), prod_d(ab, c)),
        pn == (a.n() * b.n()) * c.n(),
        pd == (a.d() * b.d()) * c.d(),
    ensures
        q_is(left, pn, pd),
{
    let ad = a.d();
    let bd = b.d();
    let cd = c.d();
    let ld = left.d();
    assert(left.n() * (ab.d() * cd) == (ab.n() * c.n()) * ld);
    assert((left.n() * (ab.d() * cd)) * (ad * bd) == ((ab.n() * c.n()) * ld) * (ad * bd));
    assert((left.n() * (ab.d() * cd)) * (ad * bd) == ab.d() * (left.n() * ((ad * bd) * cd)))
        by (nonlinear_arith);
    assert(left.n() * ((ad * bd) * cd) == left.n() * pd);
    assert(((ab.n() * c.n()) * ld) * (ad * bd) == (ab.n() * (ad * bd)) * (c.n() * ld))
        by (nonlinear_arith);
    assert(ab.n() * (ad * bd) == (a.n() * b.n()) * ab.d());
    assert((ab.n() * (ad * bd)) * (c.n() * ld) == ((a.n() * b.n()) * ab.d()) * (c.n() * ld));
    assert(((a.n() * b.n()) * ab.d()) * (c.n() * ld) == ab.d() * (((a.n() * b.n()) * c.n()) * ld))
        by (nonlinear_arith);
    assert(((a.n() * b.n()) * c.n()) * ld == pn * ld);
    assert(ab.d() * (left.n() * pd) == ab.d() * (pn * ld));
    assert((left.n() * pd) * ab.d() == (pn * ld) * ab.d()) by (nonlinear_arith)
        requires
            ab.d() * (left.n() * pd) == ab.d() * (pn * ld),
    ;
    lemma_cancel_pos(left.n() * pd, pn * ld, ab.d());
}

/// `a·(b·c)` denotes the same product.
pub proof fn lemma_mul_chain_value_right(a: Rat, b: Rat, c: Rat, bc: Rat, right: Rat, pn: int, pd: int)
    requires
        a.wf(),
        b.wf(),
        c.wf(),
        bc.wf(),
        right.wf(),
        q_is(bc, mul_n(b, c), prod_d(b, c)),
        q_is(right, mul_n(a, bc), prod_d(a, bc)),
        pn == (a.n() * b.n()) * c.n(),
        pd == (a.d() * b.d()) * c.d(),
    ensures
        q_is(right, pn, pd),
{
    let ad = a.d();
    let bd = b.d();
    let cd = c.d();
    let rd = right.d();
    assert(right.n() * (ad * bc.d()) == (a.n() * bc.n()) * rd);
    assert((right.n() * (ad * bc.d())) * (bd * cd) == ((a.n() * bc.n()) * rd) * (bd * cd));
    assert((right.n() * (ad * bc.d())) * (bd * cd) == bc.d() * (right.n() * ((ad * bd) * cd)))
        by (nonlinear_arith);
    assert(right.n() * ((ad * bd) * cd) == right.n() * pd);
    assert(((a.n() * bc.n()) * rd) * (bd * cd) == (bc.n() * (bd * cd)) * (a.n() * rd))
        by (nonlinear_arith);
    assert(bc.n() * (bd * cd) == (b.n() * c.n()) * bc.d());
    assert((bc.n() * (bd * cd)) * (a.n() * rd) == ((b.n() * c.n()) * bc.d()) * (a.n() * rd));
    assert(((b.n() * c.n()) * bc.d()) * (a.n() * rd) == bc.d() * (((a.n() * b.n()) * c.n()) * rd))
        by (nonlinear_arith);
    assert(((a.n() * b.n()) * c.n()) * rd == pn * rd);
    assert(bc.d() * (right.n() * pd) == bc.d() * (pn * rd));
    assert((right.n() * pd) * bc.d() == (pn * rd) * bc.d()) by (nonlinear_arith)
        requires
            bc.d() * (right.n() * pd) == bc.d() * (pn * rd),
    ;
    lemma_cancel_pos(right.n() * pd, pn * rd, bc.d());
}

/// **Distributivity on the exact path:** `a·(b + c) == a·b + a·c`.
///
/// Both sides are reduced to a common fraction the same way as the two
/// associativity theorems, then compared once.
pub proof fn theorem_distributive_exact(
    a: Rat,
    b: Rat,
    c: Rat,
    bc: Rat,
    lhs: Rat,
    ab: Rat,
    ac: Rat,
    rhs: Rat,
)
    requires
        a.wf(),
        b.wf(),
        c.wf(),
        bc.wf(),
        lhs.wf(),
        ab.wf(),
        ac.wf(),
        rhs.wf(),
        q_is(bc, add_n(b, c), prod_d(b, c)),
        q_is(lhs, mul_n(a, bc), prod_d(a, bc)),
        q_is(ab, mul_n(a, b), prod_d(a, b)),
        q_is(ac, mul_n(a, c), prod_d(a, c)),
        q_is(rhs, add_n(ab, ac), prod_d(ab, ac)),
    ensures
        q_eq(lhs, rhs),
{
    let dn = a.n() * (b.n() * c.d() + c.n() * b.d());
    let dd = a.d() * (b.d() * c.d());
    assert(dd > 0) by (nonlinear_arith)
        requires
            dd == a.d() * (b.d() * c.d()),
            a.d() > 0,
            b.d() > 0,
            c.d() > 0,
    ;
    lemma_distrib_lhs_value(a, b, c, bc, lhs, dn, dd);
    lemma_distrib_rhs_value(a, b, c, ab, ac, rhs, dn, dd);
    lemma_same_value_eq(lhs, rhs, dn, dd);
}

/// `a·(b + c)` denotes `a.n·(b.n·c.d + c.n·b.d) / (a.d·b.d·c.d)`.
pub proof fn lemma_distrib_lhs_value(a: Rat, b: Rat, c: Rat, bc: Rat, lhs: Rat, dn: int, dd: int)
    requires
        a.wf(),
        b.wf(),
        c.wf(),
        bc.wf(),
        lhs.wf(),
        q_is(bc, add_n(b, c), prod_d(b, c)),
        q_is(lhs, mul_n(a, bc), prod_d(a, bc)),
        dn == a.n() * (b.n() * c.d() + c.n() * b.d()),
        dd == a.d() * (b.d() * c.d()),
    ensures
        q_is(lhs, dn, dd),
{
    let ad = a.d();
    let bd = b.d();
    let cd = c.d();
    let nbc = b.n() * cd + c.n() * bd;
    let ld = lhs.d();
    assert(lhs.n() * (ad * bc.d()) == (a.n() * bc.n()) * ld);
    assert((lhs.n() * (ad * bc.d())) * (bd * cd) == ((a.n() * bc.n()) * ld) * (bd * cd));
    assert((lhs.n() * (ad * bc.d())) * (bd * cd) == bc.d() * (lhs.n() * (ad * (bd * cd))))
        by (nonlinear_arith);
    assert(lhs.n() * (ad * (bd * cd)) == lhs.n() * dd);
    assert(((a.n() * bc.n()) * ld) * (bd * cd) == (bc.n() * (bd * cd)) * (a.n() * ld))
        by (nonlinear_arith);
    assert(bc.n() * (bd * cd) == nbc * bc.d());
    assert((bc.n() * (bd * cd)) * (a.n() * ld) == (nbc * bc.d()) * (a.n() * ld));
    assert((nbc * bc.d()) * (a.n() * ld) == bc.d() * ((a.n() * nbc) * ld)) by (nonlinear_arith);
    assert((a.n() * nbc) * ld == dn * ld);
    assert(bc.d() * (lhs.n() * dd) == bc.d() * (dn * ld));
    assert((lhs.n() * dd) * bc.d() == (dn * ld) * bc.d()) by (nonlinear_arith)
        requires
            bc.d() * (lhs.n() * dd) == bc.d() * (dn * ld),
    ;
    lemma_cancel_pos(lhs.n() * dd, dn * ld, bc.d());
}

/// `a·b + a·c` denotes the same fraction.
///
/// Scale the sum's cross-multiplication by `(a.d·b.d)·(a.d·c.d)`, substitute
/// both products, cancel `ab.d·ac.d`, and what is left is a pure ring identity.
pub proof fn lemma_distrib_rhs_value(a: Rat, b: Rat, c: Rat, ab: Rat, ac: Rat, rhs: Rat, dn: int, dd: int)
    requires
        a.wf(),
        b.wf(),
        c.wf(),
        ab.wf(),
        ac.wf(),
        rhs.wf(),
        q_is(ab, mul_n(a, b), prod_d(a, b)),
        q_is(ac, mul_n(a, c), prod_d(a, c)),
        q_is(rhs, add_n(ab, ac), prod_d(ab, ac)),
        dn == a.n() * (b.n() * c.d() + c.n() * b.d()),
        dd == a.d() * (b.d() * c.d()),
    ensures
        q_is(rhs, dn, dd),
{
    let ad = a.d();
    let bd = b.d();
    let cd = c.d();
    let rd = rhs.d();
    let g = ab.d() * ac.d();
    let k = (ad * bd) * (ad * cd);
    assert(g > 0) by (nonlinear_arith)
        requires
            g == ab.d() * ac.d(),
            ab.d() > 0,
            ac.d() > 0,
    ;
    assert(k > 0) by (nonlinear_arith)
        requires
            k == (ad * bd) * (ad * cd),
            ad > 0,
            bd > 0,
            cd > 0,
    ;
    // The sum relation, scaled by k.
    assert(rhs.n() * g == (ab.n() * ac.d() + ac.n() * ab.d()) * rd);
    assert((rhs.n() * g) * k == ((ab.n() * ac.d() + ac.n() * ab.d()) * rd) * k);
    // Distribute the right side and rearrange each half so the two product
    // relations can be substituted.
    // Distribution and rearrangement have to be separate steps: a single
    // partially-factored identity over seven atoms exhausts the rlimit, and
    // `k` is a local, so its definition has to travel into each block.
    assert(((ab.n() * ac.d() + ac.n() * ab.d()) * rd) * k == ((ab.n() * ac.d()) * rd) * k + ((
    ac.n() * ab.d()) * rd) * k) by (nonlinear_arith);
    assert(((ab.n() * ac.d()) * rd) * k == ((ab.n() * (ad * bd)) * (ac.d() * (ad * cd))) * rd)
        by (nonlinear_arith)
        requires
            k == (ad * bd) * (ad * cd),
    ;
    assert(((ac.n() * ab.d()) * rd) * k == ((ac.n() * (ad * cd)) * (ab.d() * (ad * bd))) * rd)
        by (nonlinear_arith)
        requires
            k == (ad * bd) * (ad * cd),
    ;
    assert(ab.n() * (ad * bd) == (a.n() * b.n()) * ab.d());
    assert(ac.n() * (ad * cd) == (a.n() * c.n()) * ac.d());
    assert(((ab.n() * (ad * bd)) * (ac.d() * (ad * cd))) * rd == (((a.n() * b.n()) * ab.d()) * (
    ac.d() * (ad * cd))) * rd);
    assert(((ac.n() * (ad * cd)) * (ab.d() * (ad * bd))) * rd == (((a.n() * c.n()) * ac.d()) * (
    ab.d() * (ad * bd))) * rd);
    // Both halves carry the factor g == ab.d·ac.d.
    let u = (a.n() * b.n()) * (ad * cd);
    let v = (a.n() * c.n()) * (ad * bd);
    assert((((a.n() * b.n()) * ab.d()) * (ac.d() * (ad * cd))) * rd == g * (u * rd))
        by (nonlinear_arith)
        requires
            g == ab.d() * ac.d(),
            u == (a.n() * b.n()) * (ad * cd),
    ;
    assert((((a.n() * c.n()) * ac.d()) * (ab.d() * (ad * bd))) * rd == g * (v * rd))
        by (nonlinear_arith)
        requires
            g == ab.d() * ac.d(),
            v == (a.n() * c.n()) * (ad * bd),
    ;
    assert(g * (u * rd) + g * (v * rd) == g * ((u + v) * rd)) by (nonlinear_arith);
    assert((rhs.n() * g) * k == g * (rhs.n() * k)) by (nonlinear_arith);
    assert(g * (rhs.n() * k) == g * ((u + v) * rd));
    assert((rhs.n() * k) * g == ((u + v) * rd) * g) by (nonlinear_arith)
        requires
            g * (rhs.n() * k) == g * ((u + v) * rd),
    ;
    lemma_cancel_pos(rhs.n() * k, (u + v) * rd, g);
    // What remains is pure ring: k == ad·dd and u + v == ad·dn.
    assert(k == ad * dd) by (nonlinear_arith)
        requires
            k == (ad * bd) * (ad * cd),
            dd == ad * (bd * cd),
    ;
    assert(ad * dn == ad * (a.n() * (b.n() * cd)) + ad * (a.n() * (c.n() * bd)))
        by (nonlinear_arith)
        requires
            dn == a.n() * (b.n() * cd + c.n() * bd),
    ;
    assert(u == ad * (a.n() * (b.n() * cd))) by (nonlinear_arith)
        requires
            u == (a.n() * b.n()) * (ad * cd),
    ;
    assert(v == ad * (a.n() * (c.n() * bd))) by (nonlinear_arith)
        requires
            v == (a.n() * c.n()) * (ad * bd),
    ;
    assert(rhs.n() * (ad * dd) == (ad * dn) * rd);
    assert((rhs.n() * dd) * ad == (dn * rd) * ad) by (nonlinear_arith)
        requires
            rhs.n() * (ad * dd) == (ad * dn) * rd,
    ;
    lemma_cancel_pos(rhs.n() * dd, dn * rd, ad);
}

/// Additive and multiplicative identities are exact.
pub proof fn theorem_identities(a: Rat, dir: Dir)
    requires
        a.wf(),
    ensures
        ({
            let z = Rat { num: 0, den: 1 };
            let o = Rat { num: 1, den: 1 };
            &&& exact_path(add_n(a, z), prod_d(a, z))
            &&& exact_path(mul_n(a, o), prod_d(a, o))
            &&& round_frac(add_n(a, z), prod_d(a, z), dir) == a
            &&& round_frac(mul_n(a, o), prod_d(a, o), dir) == a
        }),
{
    let z = Rat { num: 0, den: 1 };
    let o = Rat { num: 1, den: 1 };
    assert(add_n(a, z) == a.n() && prod_d(a, z) == a.d());
    assert(mul_n(a, o) == a.n() && prod_d(a, o) == a.d());
    crate::round::lemma_r1_identity(a.n(), a.d(), dir);
    lemma_round_of_wf_is_self(a, dir);
}

/// Rounding a value that is already a well-formed `Rat` returns it unchanged.
pub proof fn lemma_round_of_wf_is_self(a: Rat, dir: Dir)
    requires
        a.wf(),
    ensures
        round_frac(a.n(), a.d(), dir) == a,
{
    if a.n() == 0 {
        assert(a.d() == 1);
    } else {
        assert(gcd_int(a.n(), a.d()) == 1);
        assert(crate::round::red_num(a.n(), a.d()) == a.n());
        assert(crate::round::red_den(a.n(), a.d()) == a.d());
        assert(crate::model::magnitude_fits(a.n(), a.d())) by (nonlinear_arith)
            requires
                abs_int(a.n()) <= crate::model::max_mag(),
                a.d() >= 1,
                crate::model::max_mag() > 0,
        ;
    }
}

// ---------------------------------------------------------------------------
// Order laws
// ---------------------------------------------------------------------------

/// **`Ord` is a total order** and it agrees with the ghost order.
///
/// `Rat` has no `NaN`. There is therefore no incomparable pair, and
/// `PartialOrd` never returns `None`.
pub proof fn theorem_order_total(a: Rat, b: Rat, c: Rat)
    requires
        a.wf(),
        b.wf(),
        c.wf(),
    ensures
        q_le(a, a),
        q_le(a, b) || q_le(b, a),
        (q_le(a, b) && q_le(b, a)) ==> a == b,
        (q_le(a, b) && q_le(b, c)) ==> q_le(a, c),
        q_lt(a, b) <==> (q_le(a, b) && !q_eq(a, b)),
{
    crate::q::lemma_le_trans(a, b, c);
    if q_le(a, b) && q_le(b, a) {
        assert(q_eq(a, b));
        lemma_canonical_eq(a, b);
    }
}

// ---------------------------------------------------------------------------
// Involutions
// ---------------------------------------------------------------------------

/// `-(-a) == a`, `abs(abs(a)) == abs(a)`, `abs(-a) == abs(a)`.
pub proof fn theorem_neg_abs_involution(a: Rat)
    requires
        a.wf(),
    ensures
        ({
            let na = Rat { num: (-a.n()) as i64, den: a.den };
            let aa = Rat { num: abs_int(a.n()) as i64, den: a.den };
            &&& Rat { num: (-(na.n())) as i64, den: na.den } == a
            &&& Rat { num: abs_int(aa.n()) as i64, den: aa.den } == aa
        }),
{
}

/// `1/(1/a) == a` for non-zero `a`. Reciprocal is exact in both directions.
/// This is thus a genuine involution, with no rounding at any step.
pub proof fn theorem_recip_involution(a: Rat, r: Rat, rr: Rat)
    requires
        a.wf(),
        r.wf(),
        rr.wf(),
        a.n() != 0,
        crate::q::q_is_recip(r, a),
        crate::q::q_is_recip(rr, r),
    ensures
        q_eq(rr, a),
{
    assert(r.n() != 0) by (nonlinear_arith)
        requires
            r.n() * a.n() == a.d() * r.d(),
            a.d() > 0,
            r.d() > 0,
    ;
    assert(rr.n() * a.d() == a.n() * rr.d()) by (nonlinear_arith)
        requires
            r.n() * a.n() == a.d() * r.d(),
            rr.n() * r.n() == r.d() * rr.d(),
            a.d() > 0,
            r.d() > 0,
            rr.d() > 0,
            a.n() != 0,
            r.n() != 0,
    ;
}

/// `a - b == a + (-b)` on the exact path.
pub proof fn theorem_sub_is_add_neg(a: Rat, b: Rat)
    requires
        a.wf(),
        b.wf(),
    ensures
        ({
            let nb = Rat { num: (-b.n()) as i64, den: b.den };
            sub_n(a, b) == add_n(a, nb) && prod_d(a, b) == prod_d(a, nb)
        }),
{
    crate::model::lemma_max_mag_pow2();
    // Pushing the negation through the product is nonlinear.
    assert((-b.n()) * a.d() == -(b.n() * a.d())) by (nonlinear_arith);
}

/// `a / b == a * (1/b)` as exact rationals.
pub proof fn theorem_div_is_mul_recip(a: Rat, b: Rat, rb: Rat)
    requires
        a.wf(),
        b.wf(),
        rb.wf(),
        b.n() != 0,
        crate::q::q_is_recip(rb, b),
    ensures
        div_n(a, b) * prod_d(a, rb) == mul_n(a, rb) * div_d(a, b),
{
    assert(div_n(a, b) * prod_d(a, rb) == mul_n(a, rb) * div_d(a, b)) by (nonlinear_arith)
        requires
            rb.n() * b.n() == b.d() * rb.d(),
            a.d() > 0,
            b.d() > 0,
            rb.d() > 0,
            b.n() != 0,
    ;
}

// ---------------------------------------------------------------------------
// Associativity up to a proven error bound
//
// `theorem_add_associative_exact` above states the exact-path case. This
// section bounds the distance between `(a+b)+c` and `a+(b+c)` when rounding
// occurs.
//
// Both bracketings round the *same* exact value `a+b+c` through two rounding
// steps apiece. Each step costs at most one R3 unit against its own input.
// Error propagates through exact addition unchanged. This is the fact
// `crate::lipschitz::lemma_abs_error_step` uses for the V8 fold bound. The two
// 2-unit paths are therefore at most `4` units apart, by the triangle
// inequality.
// ---------------------------------------------------------------------------

/// A value equal to itself carries zero accumulated error against any budget.
/// Every chain below starts from this base case. A value `a` is not the output
/// of any rounding, and is thus a perfect approximation of itself.
pub proof fn lemma_self_zero_error(x: Rat, m: int)
    requires
        x.wf(),
    ensures
        within_abs_error(x, x.n(), x.d(), 0, m),
{
    assert(x.n() * x.d() - x.n() * x.d() == 0);
    assert(abs_int(0) == 0);
}

/// `|x| == |-x|`, stated for [`abs_int`] specifically. [`abs_int`] is defined
/// by a sign case split. Verus's nonlinear tactic does not derive this fact on
/// its own.
pub proof fn lemma_abs_int_neg(x: int)
    ensures
        abs_int(-x) == abs_int(x),
{
}

/// The ring identity underlying both bracketings of `a + b + c`: combining
/// `a, b` first and then folding in `c` reaches the same numerator/denominator
/// pair (up to reassociation) as combining `b, c` first and folding in `a`.
/// Neither side has to be exact. This is pure algebra on the *exact* numerators
/// and denominators that the two additions compute.
pub proof fn lemma_sum3_ring(a: Rat, b: Rat, c: Rat)
    requires
        a.wf(),
        b.wf(),
        c.wf(),
    ensures
        add_n(a, b) * c.d() + c.n() * prod_d(a, b) == add_n(b, c) * a.d() + a.n() * prod_d(b, c),
        prod_d(a, b) * c.d() == prod_d(b, c) * a.d(),
{
    let ad = a.d();
    let an = a.n();
    let bd = b.d();
    let bn = b.n();
    let cd = c.d();
    let cn = c.n();
    // Unfold `add_n`/`prod_d` to plain arithmetic *before* handing anything to
    // `nonlinear_arith`: that tactic sees function applications as opaque
    // terms, not their definitions, unless an equality is supplied.
    assert(add_n(a, b) == an * bd + bn * ad);
    assert(prod_d(a, b) == ad * bd);
    assert(add_n(b, c) == bn * cd + cn * bd);
    assert(prod_d(b, c) == bd * cd);
    // The two three-monomial expansions match term for term, up to
    // reassociation. This is a single ring identity over six named atoms.
    assert((an * bd + bn * ad) * cd + cn * (ad * bd) == (bn * cd + cn * bd) * ad + an * (bd * cd))
        by (nonlinear_arith);
    assert(ad * bd * cd == bd * cd * ad) by (nonlinear_arith);
}

/// **Associativity up to a proven error, for `add`.**
///
/// `(a+b)+c` and `a+(b+c)` are rounded approximations of the same exact value
/// `a + b + c`. Each bracketing does exactly two rounding steps. By R3, each
/// step adds at most one unit of `2^-61 · m` error to its own input, where `m`
/// bounds the magnitude of that input. Addition is exactly 1-Lipschitz, so an
/// error that is already present passes through the exact addition unchanged.
/// Each bracketing is thus within `2` units of the true sum. The triangle
/// inequality bounds the distance between the two bracketings by `4` units:
///
/// `|((a+b)+c) - (a+(b+c))| <= 4 · 2^-61 · m`.
///
/// The hypotheses are the per-step non-saturation and magnitude bounds that R3
/// needs, for all four additions in the two bracketings. This is the shape that
/// [`crate::nary::fold_bounded`] uses for the V8 sum bound, applied to a tree of
/// depth two instead of a left fold. The bound needs no `[0, 1]` hypothesis.
/// The caller selects `m` to fit its own domain. For example, opinion
/// components are in `[0, 1]`, and partial sums of three of them stay below
/// `m == 3`. The defect is then at most `12 · 2^-61 ≈ 5.2 · 10^-18`.
pub proof fn theorem_add_associativity_bound(a: Rat, b: Rat, c: Rat, dir: Dir, m: int)
    requires
        a.wf(),
        b.wf(),
        c.wf(),
        m >= 1,
        !saturated(add_n(a, b), prod_d(a, b)),
        max_int(prod_d(a, b), abs_int(add_n(a, b))) <= m * prod_d(a, b),
        !saturated(add_n(b, c), prod_d(b, c)),
        max_int(prod_d(b, c), abs_int(add_n(b, c))) <= m * prod_d(b, c),
        ({
            let ab = round_frac(add_n(a, b), prod_d(a, b), dir);
            &&& !saturated(add_n(ab, c), prod_d(ab, c))
            &&& max_int(prod_d(ab, c), abs_int(add_n(ab, c))) <= m * prod_d(ab, c)
        }),
        ({
            let bc = round_frac(add_n(b, c), prod_d(b, c), dir);
            &&& !saturated(add_n(a, bc), prod_d(a, bc))
            &&& max_int(prod_d(a, bc), abs_int(add_n(a, bc))) <= m * prod_d(a, bc)
        }),
    ensures
        ({
            let ab = round_frac(add_n(a, b), prod_d(a, b), dir);
            let bc = round_frac(add_n(b, c), prod_d(b, c), dir);
            let left = round_frac(add_n(ab, c), prod_d(ab, c), dir);
            let right = round_frac(add_n(a, bc), prod_d(a, bc), dir);
            within_abs_error(left, right.n(), right.d(), 4, m)
        }),
{
    crate::q::lemma_op_widths(a, b);
    crate::q::lemma_op_widths(b, c);
    let ab = round_frac(add_n(a, b), prod_d(a, b), dir);
    let bc = round_frac(add_n(b, c), prod_d(b, c), dir);
    crate::round::lemma_round_frac_wf(add_n(a, b), prod_d(a, b), dir);
    crate::round::lemma_round_frac_wf(add_n(b, c), prod_d(b, c), dir);
    crate::q::lemma_op_widths(ab, c);
    crate::q::lemma_op_widths(a, bc);
    crate::q::lemma_op_widths(bc, a);
    let left = round_frac(add_n(ab, c), prod_d(ab, c), dir);
    let right = round_frac(add_n(a, bc), prod_d(a, bc), dir);
    crate::round::lemma_round_frac_wf(add_n(ab, c), prod_d(ab, c), dir);
    crate::round::lemma_round_frac_wf(add_n(a, bc), prod_d(a, bc), dir);

    // --- left bracketing: a (0 units) -> ab (1 unit) -> left (2 units) ---
    lemma_self_zero_error(a, m);
    crate::round::lemma_r3_error(add_n(a, b), prod_d(a, b), dir);
    crate::lipschitz::lemma_abs_error_step(a, a.n(), a.d(), b, ab, 0, m);
    crate::round::lemma_r3_error(add_n(ab, c), prod_d(ab, c), dir);
    crate::lipschitz::lemma_abs_error_step(ab, add_n(a, b), prod_d(a, b), c, left, 1, m);

    let sn = add_n(a, b) * c.d() + c.n() * prod_d(a, b);
    let sd = prod_d(a, b) * c.d();
    assert(within_abs_error(left, sn, sd, 2, m));

    // --- right bracketing: b (0 units) -> bc (1 unit) -> right (2 units).
    // The step folds `a` into `bc` on the right. `add_n` and `prod_d` are
    // symmetric formulas, which identifies the result with `right`. ---
    lemma_self_zero_error(b, m);
    crate::round::lemma_r3_error(add_n(b, c), prod_d(b, c), dir);
    crate::lipschitz::lemma_abs_error_step(b, b.n(), b.d(), c, bc, 0, m);

    assert(add_n(bc, a) == add_n(a, bc));
    assert(prod_d(bc, a) == bc.d() * a.d());
    assert(prod_d(a, bc) == a.d() * bc.d());
    assert(bc.d() * a.d() == a.d() * bc.d()) by (nonlinear_arith);
    assert(prod_d(bc, a) == prod_d(a, bc));
    crate::round::lemma_r3_error(add_n(a, bc), prod_d(a, bc), dir);
    assert(within_error_bound(right, add_n(bc, a), prod_d(bc, a)));
    assert(max_int(prod_d(bc, a), abs_int(add_n(bc, a))) <= m * prod_d(bc, a));
    crate::lipschitz::lemma_abs_error_step(bc, add_n(b, c), prod_d(b, c), a, right, 1, m);

    lemma_sum3_ring(a, b, c);
    assert(within_abs_error(right, sn, sd, 2, m));

    // --- combine the two 2-unit bounds via the triangle inequality ---
    crate::model::lemma_pow2_pos(precision_b());
    assert(left.d() > 0);
    assert(right.d() > 0);
    assert(sd > 0) by (nonlinear_arith)
        requires
            sd == prod_d(a, b) * c.d(),
            prod_d(a, b) > 0,
            c.d() > 0,
    ;
    lemma_abs_int_neg(right.n() * sd - sn * right.d());
    assert(sn * right.d() - right.n() * sd == -(right.n() * sd - sn * right.d()));
    assert(abs_int(sn * right.d() - right.n() * sd) == abs_int(right.n() * sd - sn * right.d()));
    assert(abs_int(right.n() * sd - sn * right.d()) * pow2(precision_b()) <= 2 * m * (right.d()
        * sd));
    assert(right.d() * sd == sd * right.d()) by (nonlinear_arith);
    assert(abs_int(sn * right.d() - right.n() * sd) * pow2(precision_b()) <= 2 * m * (sd
        * right.d()));
    crate::lipschitz::lemma_frac_triangle(
        left.n(),
        left.d(),
        sn,
        sd,
        right.n(),
        right.d(),
        2 * m,
        2 * m,
        pow2(precision_b()),
    );
}

// ---------------------------------------------------------------------------
// Associativity up to a proven error, for `mul`
//
// `mul` accumulates error differently from `add`. Addition has a Lipschitz
// constant of exactly `1` in each argument. Thus magnitude bounds on the sums
// are sufficient for `theorem_add_associativity_bound`. Multiplication scales
// an existing error by the magnitude of the other factor
// (`crate::lipschitz::lemma_mul_lipschitz`). A general bound thus needs a
// magnitude parameter for the products and for the individual factors, and the
// defect grows with the square of that bound.
//
// On `[0, 1]` this effect disappears. Every relevant magnitude is at most `1`,
// or is close to `1` for a once-rounded intermediate. This section proves the
// bound under that hypothesis.
// ---------------------------------------------------------------------------

/// A cross-multiplied inequality survives cancelling a shared positive factor.
pub proof fn lemma_cancel_pos_le(x: int, y: int, c: int)
    requires
        c > 0,
        x * c <= y * c,
    ensures
        x <= y,
{
    assert(x <= y) by (nonlinear_arith)
        requires
            c > 0,
            x * c <= y * c,
    ;
}

/// `|x·y| == |x|·y` for `y >= 0`. This lemma widens
/// [`crate::model::lemma_abs_mul_pos`] to cover the `y == 0` edge, which that
/// lemma's strict `c > 0` excludes.
pub proof fn lemma_abs_mul_nonneg(x: int, y: int)
    requires
        y >= 0,
    ensures
        abs_int(x * y) == abs_int(x) * y,
{
    if y == 0 {
        assert(x * y == 0) by (nonlinear_arith)
            requires
                y == 0,
        ;
        assert(abs_int(x) * y == 0) by (nonlinear_arith)
            requires
                y == 0,
        ;
    } else {
        crate::model::lemma_abs_mul_pos(x, y);
    }
}

/// The exact product of two `[0, 1]` values is itself in `[0, 1]`.
pub proof fn lemma_unit_interval_mul(a: Rat, b: Rat)
    requires
        a.wf(),
        b.wf(),
        0 <= a.n(),
        a.n() <= a.d(),
        0 <= b.n(),
        b.n() <= b.d(),
    ensures
        0 <= mul_n(a, b),
        mul_n(a, b) <= prod_d(a, b),
{
    assert(mul_n(a, b) == a.n() * b.n());
    assert(prod_d(a, b) == a.d() * b.d());
    assert(a.n() * b.n() >= 0) by (nonlinear_arith)
        requires
            a.n() >= 0,
            b.n() >= 0,
    ;
    assert(a.n() * b.n() <= a.d() * b.n()) by (nonlinear_arith)
        requires
            a.n() <= a.d(),
            b.n() >= 0,
    ;
    assert(a.d() * b.n() <= a.d() * b.d()) by (nonlinear_arith)
        requires
            b.n() <= b.d(),
            a.d() > 0,
    ;
    assert(mul_n(a, b) <= prod_d(a, b));
}

/// A `[0, 1]` product, rounded: the result is within one absolute-error unit
/// of the exact product, and its magnitude is at most `2` (the exact product
/// is at most `1`, and one grid step cannot push it far past that).
pub proof fn lemma_rounded_product_bound(a: Rat, b: Rat, dir: Dir)
    requires
        a.wf(),
        b.wf(),
        0 <= a.n(),
        a.n() <= a.d(),
        0 <= b.n(),
        b.n() <= b.d(),
        !saturated(mul_n(a, b), prod_d(a, b)),
    ensures
        ({
            let ab = round_frac(mul_n(a, b), prod_d(a, b), dir);
            &&& ab.wf()
            &&& within_abs_error(ab, mul_n(a, b), prod_d(a, b), 1, 1)
            &&& -ab.d() <= ab.n()
            &&& ab.n() <= 2 * ab.d()
            &&& abs_int(ab.n()) <= 2 * ab.d()
        }),
{
    lemma_unit_interval_mul(a, b);
    crate::q::lemma_op_widths(a, b);
    crate::round::lemma_round_frac_wf(mul_n(a, b), prod_d(a, b), dir);
    crate::round::lemma_r3_error(mul_n(a, b), prod_d(a, b), dir);
    crate::model::lemma_pow2_pos(precision_b());
    let ab = round_frac(mul_n(a, b), prod_d(a, b), dir);
    let pn = mul_n(a, b);
    let pd = prod_d(a, b);
    assert(pd > 0);
    assert(abs_int(pn) == pn);
    assert(max_int(pd, abs_int(pn)) == pd);
    assert(abs_int(ab.n() * pd - pn * ab.d()) * pow2(precision_b()) <= ab.d() * pd);
    assert(within_abs_error(ab, pn, pd, 1, 1));
    assert(pow2(precision_b()) >= 1);
    let diff = ab.n() * pd - pn * ab.d();
    assert(abs_int(diff) >= 0);
    assert(abs_int(diff) <= abs_int(diff) * pow2(precision_b())) by (nonlinear_arith)
        requires
            abs_int(diff) >= 0,
            pow2(precision_b()) >= 1,
    ;
    assert(abs_int(diff) <= ab.d() * pd);
    // Upper bound: ab.n()·pd <= pn·ab.d() + ab.d()·pd <= 2·(ab.d()·pd).
    assert(ab.n() * pd <= pn * ab.d() + ab.d() * pd) by (nonlinear_arith)
        requires
            diff == ab.n() * pd - pn * ab.d(),
            abs_int(diff) <= ab.d() * pd,
    ;
    assert(pn * ab.d() <= pd * ab.d()) by (nonlinear_arith)
        requires
            pn <= pd,
            ab.d() > 0,
    ;
    assert(ab.n() * pd <= pd * ab.d() + ab.d() * pd) by (nonlinear_arith)
        requires
            ab.n() * pd <= pn * ab.d() + ab.d() * pd,
            pn * ab.d() <= pd * ab.d(),
    ;
    assert(pd * ab.d() + ab.d() * pd == (2 * ab.d()) * pd) by (nonlinear_arith);
    assert(ab.n() * pd <= (2 * ab.d()) * pd);
    lemma_cancel_pos_le(ab.n(), 2 * ab.d(), pd);
    // Lower bound: ab.n()·pd >= pn·ab.d() - ab.d()·pd >= -(ab.d()·pd).
    assert(ab.n() * pd >= pn * ab.d() - ab.d() * pd) by (nonlinear_arith)
        requires
            diff == ab.n() * pd - pn * ab.d(),
            abs_int(diff) <= ab.d() * pd,
    ;
    assert(pn * ab.d() >= 0) by (nonlinear_arith)
        requires
            pn >= 0,
            ab.d() > 0,
    ;
    assert(ab.n() * pd >= 0 - ab.d() * pd) by (nonlinear_arith)
        requires
            ab.n() * pd >= pn * ab.d() - ab.d() * pd,
            pn * ab.d() >= 0,
    ;
    assert((-ab.d()) * pd == 0 - ab.d() * pd) by (nonlinear_arith);
    assert((-ab.d()) * pd <= ab.n() * pd);
    lemma_cancel_pos_le(-ab.d(), ab.n(), pd);
    assert(abs_int(ab.n()) <= 2 * ab.d());
}

/// Scaling a bounded rational error by a `[0, 1]` value does not increase it.
/// If `|X - Y| <= e/ed` and `0 <= C <= 1`, then `|X·C - Y·C| <= e/ed` as well.
/// The statement is division-free. Both fractions carry a scaling by `C`'s
/// numerator and denominator.
pub proof fn lemma_frac_scale_nonneg(xn: int, xd: int, yn: int, yd: int, cn: int, cd: int, e: int, ed: int)
    requires
        xd > 0,
        yd > 0,
        cd > 0,
        ed > 0,
        e >= 0,
        0 <= cn <= cd,
        abs_int(xn * yd - yn * xd) * ed <= e * (xd * yd),
    ensures
        abs_int((xn * cn) * (yd * cd) - (yn * cn) * (xd * cd)) * ed <= e * ((xd * cd) * (yd * cd)),
{
    let diffx = xn * yd - yn * xd;
    let k = cn * cd;
    // The proof splits into three small ring steps. One call that bundles the
    // reassociation and the distribution over the difference is a degree-4
    // identity over six atoms. `nonlinear_arith` does not close that reliably.
    assert((xn * cn) * (yd * cd) == k * (xn * yd)) by (nonlinear_arith)
        requires
            k == cn * cd,
    ;
    assert((yn * cn) * (xd * cd) == k * (yn * xd)) by (nonlinear_arith)
        requires
            k == cn * cd,
    ;
    assert(k * (xn * yd) - k * (yn * xd) == k * diffx) by (nonlinear_arith)
        requires
            diffx == xn * yd - yn * xd,
    ;
    assert((xn * cn) * (yd * cd) - (yn * cn) * (xd * cd) == k * diffx);
    assert(k >= 0) by (nonlinear_arith)
        requires
            cn >= 0,
            cd > 0,
            k == cn * cd,
    ;
    lemma_abs_mul_nonneg(diffx, k);
    assert(k * diffx == diffx * k) by (nonlinear_arith);
    assert(abs_int(k * diffx) == abs_int(diffx) * k);
    assert(abs_int((xn * cn) * (yd * cd) - (yn * cn) * (xd * cd)) == abs_int(diffx) * k);
    assert((abs_int(diffx) * k) * ed == k * (abs_int(diffx) * ed)) by (nonlinear_arith);
    assert(k * (abs_int(diffx) * ed) <= k * (e * (xd * yd))) by (nonlinear_arith)
        requires
            k >= 0,
            abs_int(diffx) * ed <= e * (xd * yd),
    ;
    assert(k * (e * (xd * yd)) == (cn * cd) * (e * (xd * yd))) by (nonlinear_arith)
        requires
            k == cn * cd,
    ;
    assert(cn * cd <= cd * cd) by (nonlinear_arith)
        requires
            cn <= cd,
            cd > 0,
    ;
    assert(e * (xd * yd) >= 0) by (nonlinear_arith)
        requires
            e >= 0,
            xd > 0,
            yd > 0,
    ;
    assert((cn * cd) * (e * (xd * yd)) <= (cd * cd) * (e * (xd * yd))) by (nonlinear_arith)
        requires
            cn * cd <= cd * cd,
            e * (xd * yd) >= 0,
    ;
    assert((cd * cd) * (e * (xd * yd)) == e * ((xd * cd) * (yd * cd))) by (nonlinear_arith);
    assert(abs_int((xn * cn) * (yd * cd) - (yn * cn) * (xd * cd)) * ed <= e * ((xd * cd) * (yd
        * cd)));
}

/// If `x`'s numerator is within `k` denominator-widths of zero and `y` is a
/// `[0, 1]` value, the exact product `x·y` is within `k` widths of zero as
/// well. R3 needs this magnitude bound for a second rounding step on top of
/// `x`.
pub proof fn lemma_prod_magnitude_bound(x: Rat, y: Rat, k: int)
    requires
        x.wf(),
        y.wf(),
        k >= 1,
        abs_int(x.n()) <= k * x.d(),
        0 <= y.n(),
        y.n() <= y.d(),
    ensures
        max_int(prod_d(x, y), abs_int(mul_n(x, y))) <= k * prod_d(x, y),
{
    assert(mul_n(x, y) == x.n() * y.n());
    assert(prod_d(x, y) == x.d() * y.d());
    lemma_abs_mul_nonneg(x.n(), y.n());
    assert(abs_int(x.n() * y.n()) == abs_int(x.n()) * y.n());
    assert(k * x.d() >= 0) by (nonlinear_arith)
        requires
            k >= 1,
            x.d() > 0,
    ;
    assert(abs_int(x.n()) * y.n() <= (k * x.d()) * y.n()) by (nonlinear_arith)
        requires
            abs_int(x.n()) <= k * x.d(),
            y.n() >= 0,
    ;
    assert((k * x.d()) * y.n() <= (k * x.d()) * y.d()) by (nonlinear_arith)
        requires
            y.n() <= y.d(),
            k * x.d() >= 0,
    ;
    assert((k * x.d()) * y.d() == k * (x.d() * y.d())) by (nonlinear_arith);
    assert(abs_int(mul_n(x, y)) <= k * prod_d(x, y));
    assert(prod_d(x, y) >= 0) by (nonlinear_arith)
        requires
            prod_d(x, y) == x.d() * y.d(),
            x.d() > 0,
            y.d() > 0,
    ;
    assert(prod_d(x, y) <= k * prod_d(x, y)) by (nonlinear_arith)
        requires
            prod_d(x, y) >= 0,
            k >= 1,
    ;
    assert(max_int(prod_d(x, y), abs_int(mul_n(x, y))) <= k * prod_d(x, y));
}

/// The ring identity underlying both bracketings of `a · b · c`: combining
/// `a, b` first and folding in `c` reaches the same numerator/denominator
/// product (up to reassociation) as combining `b, c` first and folding in
/// `a`. The multiplicative analogue of [`lemma_sum3_ring`].
pub proof fn lemma_mul3_ring(a: Rat, b: Rat, c: Rat)
    requires
        a.wf(),
        b.wf(),
        c.wf(),
    ensures
        mul_n(a, b) * c.n() == mul_n(b, c) * a.n(),
        prod_d(a, b) * c.d() == prod_d(b, c) * a.d(),
{
    let an = a.n();
    let ad = a.d();
    let bn = b.n();
    let bd = b.d();
    let cn = c.n();
    let cd = c.d();
    assert(mul_n(a, b) == an * bn);
    assert(mul_n(b, c) == bn * cn);
    assert(prod_d(a, b) == ad * bd);
    assert(prod_d(b, c) == bd * cd);
    assert((an * bn) * cn == (bn * cn) * an) by (nonlinear_arith);
    assert((ad * bd) * cd == (bd * cd) * ad) by (nonlinear_arith);
}

/// **Associativity up to a proven error, for `mul`, on `[0, 1]`.**
///
/// `(a·b)·c` and `a·(b·c)` are both rounded approximations of the same exact
/// product `a·b·c`. Each bracketing costs two things. The first cost is the R3
/// error of its own final rounding step. That cost is at most `2` units,
/// because a once-rounded `[0, 1]` product can have magnitude up to `2`, not
/// `1`. The second cost is the error already carried by the first rounding
/// step, scaled by the *other*, exact factor. That cost is at most `1` unit,
/// because that factor is itself in `[0, 1]`. This is the bounded-domain case
/// of `crate::lipschitz::lemma_mul_lipschitz`, with a coefficient of exactly
/// `1`. Each bracketing is thus within `3` units of the exact product. The
/// triangle inequality bounds their mutual distance by `6`:
///
/// `|((a·b)·c) - (a·(b·c))| <= 6 · 2^-61 ≈ 2.6 · 10^-18`.
///
/// This theorem covers the `[0, 1]` domain, in place of a fully general,
/// magnitude-parameterised bound. Unlike `add`, `mul` does not simply add its
/// error across steps. Each step weights the error by the *other* factor's
/// magnitude. A general bound would therefore grow with the *square* of a free
/// magnitude parameter `m`, not linearly in it. On the engine's domain that
/// magnitude is always `1`, so the distinction has no effect there. It is the
/// reason this theorem holds for `[0, 1]` rather than for an arbitrary `m`, as
/// [`theorem_add_associativity_bound`] does.
pub proof fn theorem_mul_associativity_bound_unit_interval(a: Rat, b: Rat, c: Rat, dir: Dir)
    requires
        a.wf(),
        b.wf(),
        c.wf(),
        0 <= a.n(),
        a.n() <= a.d(),
        0 <= b.n(),
        b.n() <= b.d(),
        0 <= c.n(),
        c.n() <= c.d(),
        !saturated(mul_n(a, b), prod_d(a, b)),
        !saturated(mul_n(b, c), prod_d(b, c)),
        ({
            let ab = round_frac(mul_n(a, b), prod_d(a, b), dir);
            !saturated(mul_n(ab, c), prod_d(ab, c))
        }),
        ({
            let bc = round_frac(mul_n(b, c), prod_d(b, c), dir);
            !saturated(mul_n(a, bc), prod_d(a, bc))
        }),
    ensures
        ({
            let ab = round_frac(mul_n(a, b), prod_d(a, b), dir);
            let bc = round_frac(mul_n(b, c), prod_d(b, c), dir);
            let left = round_frac(mul_n(ab, c), prod_d(ab, c), dir);
            let right = round_frac(mul_n(a, bc), prod_d(a, bc), dir);
            within_abs_error(left, right.n(), right.d(), 6, 1)
        }),
{
    lemma_rounded_product_bound(a, b, dir);
    lemma_rounded_product_bound(b, c, dir);
    let ab = round_frac(mul_n(a, b), prod_d(a, b), dir);
    let bc = round_frac(mul_n(b, c), prod_d(b, c), dir);
    crate::q::lemma_op_widths(a, b);
    crate::q::lemma_op_widths(b, c);
    crate::q::lemma_op_widths(ab, c);
    crate::q::lemma_op_widths(a, bc);
    crate::q::lemma_op_widths(bc, a);
    crate::round::lemma_round_frac_wf(mul_n(ab, c), prod_d(ab, c), dir);
    crate::round::lemma_round_frac_wf(mul_n(a, bc), prod_d(a, bc), dir);
    crate::model::lemma_pow2_pos(precision_b());
    let left = round_frac(mul_n(ab, c), prod_d(ab, c), dir);
    let right = round_frac(mul_n(a, bc), prod_d(a, bc), dir);

    let pn = a.n() * b.n() * c.n();
    let pd = a.d() * b.d() * c.d();
    assert(pd > 0) by (nonlinear_arith)
        requires
            pd == a.d() * b.d() * c.d(),
            a.d() > 0,
            b.d() > 0,
            c.d() > 0,
    ;

    // --- left: ab (1 unit) scaled by the exact, unrounded c, then left's own
    // R3 step (2 units against a magnitude-2 target). ---
    lemma_frac_scale_nonneg(ab.n(), ab.d(), mul_n(a, b), prod_d(a, b), c.n(), c.d(), 1, pow2(
        precision_b(),
    ));
    assert(mul_n(ab, c) == ab.n() * c.n());
    assert(prod_d(ab, c) == ab.d() * c.d());
    assert(mul_n(a, b) * c.n() == pn);
    assert(prod_d(a, b) * c.d() == pd);
    assert(abs_int(mul_n(ab, c) * pd - pn * prod_d(ab, c)) * pow2(precision_b()) <= 1 * (prod_d(
        ab,
        c,
    ) * pd));

    lemma_prod_magnitude_bound(ab, c, 2);
    crate::round::lemma_r3_error(mul_n(ab, c), prod_d(ab, c), dir);
    // within_error_bound gives `left.d() * max_int(...)`. The magnitude bound
    // gives `max_int(...) <= 2 * prod_d(ab,c)`. One reordering step turns that
    // into `2 * (left.d() * prod_d(ab,c))`.
    assert(left.d() * (2 * prod_d(ab, c)) == 2 * (left.d() * prod_d(ab, c))) by (nonlinear_arith);
    assert(abs_int(left.n() * prod_d(ab, c) - mul_n(ab, c) * left.d()) * pow2(precision_b())
        <= left.d() * max_int(prod_d(ab, c), abs_int(mul_n(ab, c))));
    assert(left.d() * max_int(prod_d(ab, c), abs_int(mul_n(ab, c))) <= left.d() * (2 * prod_d(
        ab,
        c,
    ))) by (nonlinear_arith)
        requires
            max_int(prod_d(ab, c), abs_int(mul_n(ab, c))) <= 2 * prod_d(ab, c),
            left.d() > 0,
    ;
    assert(within_abs_error(left, mul_n(ab, c), prod_d(ab, c), 2, 1));

    crate::lipschitz::lemma_frac_triangle(
        left.n(),
        left.d(),
        mul_n(ab, c),
        prod_d(ab, c),
        pn,
        pd,
        2,
        1,
        pow2(precision_b()),
    );
    assert(within_abs_error(left, pn, pd, 3, 1));

    // --- right: bc (1 unit) scaled by the exact, unrounded a, then right's
    // own R3 step. The step goes through `bc·a`. The symmetric formulas
    // identify the result with `right`, as in
    // `theorem_add_associativity_bound`. ---
    lemma_frac_scale_nonneg(bc.n(), bc.d(), mul_n(b, c), prod_d(b, c), a.n(), a.d(), 1, pow2(
        precision_b(),
    ));
    assert(mul_n(bc, a) == bc.n() * a.n());
    assert(prod_d(bc, a) == bc.d() * a.d());
    lemma_mul3_ring(a, b, c);
    assert(mul_n(b, c) * a.n() == pn);
    assert(prod_d(b, c) * a.d() == pd);
    assert(abs_int(mul_n(bc, a) * pd - pn * prod_d(bc, a)) * pow2(precision_b()) <= 1 * (prod_d(
        bc,
        a,
    ) * pd));

    assert(mul_n(bc, a) == mul_n(a, bc)) by (nonlinear_arith)
        requires
            mul_n(bc, a) == bc.n() * a.n(),
            mul_n(a, bc) == a.n() * bc.n(),
    ;
    assert(prod_d(bc, a) == prod_d(a, bc)) by (nonlinear_arith)
        requires
            prod_d(bc, a) == bc.d() * a.d(),
            prod_d(a, bc) == a.d() * bc.d(),
    ;

    lemma_prod_magnitude_bound(bc, a, 2);
    assert(max_int(prod_d(bc, a), abs_int(mul_n(bc, a))) <= 2 * prod_d(bc, a));
    crate::round::lemma_r3_error(mul_n(a, bc), prod_d(a, bc), dir);
    assert(within_error_bound(right, mul_n(bc, a), prod_d(bc, a)));
    assert(right.d() * (2 * prod_d(bc, a)) == 2 * (right.d() * prod_d(bc, a)))
        by (nonlinear_arith);
    assert(abs_int(right.n() * prod_d(bc, a) - mul_n(bc, a) * right.d()) * pow2(precision_b())
        <= right.d() * max_int(prod_d(bc, a), abs_int(mul_n(bc, a))));
    assert(right.d() * max_int(prod_d(bc, a), abs_int(mul_n(bc, a))) <= right.d() * (2 * prod_d(
        bc,
        a,
    ))) by (nonlinear_arith)
        requires
            max_int(prod_d(bc, a), abs_int(mul_n(bc, a))) <= 2 * prod_d(bc, a),
            right.d() > 0,
    ;
    assert(within_abs_error(right, mul_n(bc, a), prod_d(bc, a), 2, 1));

    crate::lipschitz::lemma_frac_triangle(
        right.n(),
        right.d(),
        mul_n(bc, a),
        prod_d(bc, a),
        pn,
        pd,
        2,
        1,
        pow2(precision_b()),
    );
    assert(within_abs_error(right, pn, pd, 3, 1));

    // --- combine the two 3-unit bounds via the triangle inequality ---
    lemma_abs_int_neg(right.n() * pd - pn * right.d());
    assert(pn * right.d() - right.n() * pd == -(right.n() * pd - pn * right.d()));
    assert(abs_int(pn * right.d() - right.n() * pd) == abs_int(right.n() * pd - pn * right.d()));
    assert(abs_int(right.n() * pd - pn * right.d()) * pow2(precision_b()) <= 3 * (right.d() * pd));
    assert(right.d() * pd == pd * right.d()) by (nonlinear_arith);
    assert(abs_int(pn * right.d() - right.n() * pd) * pow2(precision_b()) <= 3 * (pd
        * right.d()));

    crate::lipschitz::lemma_frac_triangle(
        left.n(),
        left.d(),
        pn,
        pd,
        right.n(),
        right.d(),
        3,
        3,
        pow2(precision_b()),
    );
}

// ---------------------------------------------------------------------------
// Order compatibility: the ordered-field laws
//
// `theorem_order_total` above states that `q_le` is a total order. This section
// states that the order is compatible with the arithmetic. Negation reverses
// the order. Addition and multiplication by a non-negative value preserve it.
// Squares sit above zero. Reciprocal reverses the order on positives. These are
// the axioms of an ordered field, stated on the exact fractions the operations
// compute before rounding. Downstream monotonicity arguments, such as "a larger
// input cannot decrease this sum", rest on them.
// ---------------------------------------------------------------------------

/// **Negation reverses the order** (and stays inside the type): the
/// numerator-negated mirror of a well-formed `Rat` is well-formed, and
/// `a <= b` holds exactly when `-b <= -a`.
///
/// The `wf` half lets ghost code build negations. Canonicality and the budget
/// are invariant under a change of sign of the numerator. The antitonicity half
/// is the ordered-group law that `Rat::neg` relies on. It turns a lower-bound
/// fact into an upper-bound fact about the negation. For example, it turns a
/// proven `min` bound into a `max` bound for negated data.
pub proof fn theorem_neg_antitone(a: Rat, b: Rat)
    requires
        a.wf(),
        b.wf(),
    ensures
        ({
            let na = Rat { num: (-a.n()) as i64, den: a.den };
            let nb = Rat { num: (-b.n()) as i64, den: b.den };
            &&& na.wf()
            &&& (q_le(a, b) <==> q_le(nb, na))
        }),
{
    let na = Rat { num: (-a.n()) as i64, den: a.den };
    let nb = Rat { num: (-b.n()) as i64, den: b.den };
    // gcd sees only |num|, which negation preserves.
    assert(abs_int(na.n()) == abs_int(a.n()));
    // Pushing the sign through each cross-product is the whole content:
    // (-b.n)·a.d <= (-a.n)·b.d is the negation, term by term, of
    // a.n·b.d <= b.n·a.d.
    assert((-b.n()) * a.d() == -(b.n() * a.d())) by (nonlinear_arith);
    assert((-a.n()) * b.d() == -(a.n() * b.d())) by (nonlinear_arith);
}

/// **`abs` is the join of `a` and `-a`**: it dominates both, and anything that
/// dominates both dominates it.
///
/// The two upper-bound clauses and the minimality clause pin `|a|` uniquely up
/// to `q_eq`, and thus, by canonicality, uniquely. The alternative
/// specification "non-negative and equal to `a` or `-a`" also admits no other
/// value. The join characterisation, however, is the form that order reasoning
/// uses. For example, it gives `|a| <= m` from the two one-sided bounds
/// `-m <= a <= m`. The evenness clause (`|-a| == |a|`, bit for bit) states what
/// [`theorem_neg_abs_involution`]'s doc comment describes but its own statement
/// omits.
pub proof fn theorem_abs_is_join(a: Rat, b: Rat)
    requires
        a.wf(),
        b.wf(),
    ensures
        ({
            let na = Rat { num: (-a.n()) as i64, den: a.den };
            let aa = Rat { num: abs_int(a.n()) as i64, den: a.den };
            let naa = Rat { num: abs_int(na.n()) as i64, den: na.den };
            &&& aa.wf()
            &&& aa.n() >= 0
            &&& q_le(a, aa)
            &&& q_le(na, aa)
            &&& (aa == a || aa == na)
            &&& naa == aa
            &&& (q_le(a, b) && q_le(na, b)) ==> q_le(aa, b)
        }),
{
    let na = Rat { num: (-a.n()) as i64, den: a.den };
    let aa = Rat { num: abs_int(a.n()) as i64, den: a.den };
    assert(abs_int(aa.n()) == abs_int(a.n()));
    // |a| dominates a: a.n <= |a.n|, scaled by the shared positive denominator.
    assert(a.n() * a.d() <= abs_int(a.n()) * a.d()) by (nonlinear_arith)
        requires
            a.d() > 0,
            a.n() <= abs_int(a.n()),
    ;
    // ...and dominates -a symmetrically.
    assert((-a.n()) * a.d() <= abs_int(a.n()) * a.d()) by (nonlinear_arith)
        requires
            a.d() > 0,
            -a.n() <= abs_int(a.n()),
    ;
    // Minimality is free once `aa` is known to be one of the two operands the
    // hypothesis already bounds.
    assert(aa == a || aa == na);
}

/// **Adding the same value to both sides preserves the order**, stated on the
/// exact fractions `add` computes: `a <= b` implies
/// `(a + c) <= (b + c)` as cross-multiplied exact sums.
///
/// This is the translation-invariance axiom of an ordered group. It concerns
/// three independent values. The conclusion compares six-term products that the
/// hypothesis does not mention. It needs no exactness or budget hypothesis,
/// because it states a fact about the mathematical sums, prior to any rounding.
pub proof fn theorem_add_monotone_exact(a: Rat, b: Rat, c: Rat)
    requires
        a.wf(),
        b.wf(),
        c.wf(),
        q_le(a, b),
    ensures
        add_n(a, c) * prod_d(b, c) <= add_n(b, c) * prod_d(a, c),
{
    let an = a.n();
    let ad = a.d();
    let bn = b.n();
    let bd = b.d();
    let cn = c.n();
    let cd = c.d();
    let s = cd * cd;
    let t = (cn * (ad * bd)) * cd;
    assert(s > 0) by (nonlinear_arith)
        requires
            s == cd * cd,
            cd > 0,
    ;
    // The hypothesis, scaled by the positive square of c's denominator.
    assert((an * bd) * s <= (bn * ad) * s) by (nonlinear_arith)
        requires
            an * bd <= bn * ad,
            s > 0,
    ;
    // Unfold the operation specs to plain arithmetic before any nonlinear
    // step. The tactic sees function applications as opaque terms.
    assert(add_n(a, c) == an * cd + cn * ad);
    assert(prod_d(b, c) == bd * cd);
    assert(add_n(b, c) == bn * cd + cn * bd);
    assert(prod_d(a, c) == ad * cd);
    // Each side distributes into the scaled hypothesis plus the same c-term,
    // in small ring steps to stay inside the resource budget.
    assert((an * cd + cn * ad) * (bd * cd) == (an * cd) * (bd * cd) + (cn * ad) * (bd * cd))
        by (nonlinear_arith);
    assert((an * cd) * (bd * cd) == (an * bd) * s) by (nonlinear_arith)
        requires
            s == cd * cd,
    ;
    assert((cn * ad) * (bd * cd) == t) by (nonlinear_arith)
        requires
            t == (cn * (ad * bd)) * cd,
    ;
    assert((bn * cd + cn * bd) * (ad * cd) == (bn * cd) * (ad * cd) + (cn * bd) * (ad * cd))
        by (nonlinear_arith);
    assert((bn * cd) * (ad * cd) == (bn * ad) * s) by (nonlinear_arith)
        requires
            s == cd * cd,
    ;
    assert((cn * bd) * (ad * cd) == t) by (nonlinear_arith)
        requires
            t == (cn * (ad * bd)) * cd,
    ;
    // Recombine: both sides are now the same linear expressions in s and t.
    assert(add_n(a, c) * prod_d(b, c) == (an * bd) * s + t);
    assert(add_n(b, c) * prod_d(a, c) == (bn * ad) * s + t);
}

/// **Multiplying both sides by a non-negative value preserves the order**,
/// stated on the exact fractions `mul` computes.
///
/// This is the other half of ordered-field compatibility. The non-negativity
/// hypothesis is necessary. For `c < 0` the conclusion is false, because the
/// order flips. [`theorem_neg_antitone`] composed with this theorem gives that
/// case.
pub proof fn theorem_mul_monotone_nonneg_exact(a: Rat, b: Rat, c: Rat)
    requires
        a.wf(),
        b.wf(),
        c.wf(),
        q_le(a, b),
        c.n() >= 0,
    ensures
        mul_n(a, c) * prod_d(b, c) <= mul_n(b, c) * prod_d(a, c),
{
    let an = a.n();
    let ad = a.d();
    let bn = b.n();
    let bd = b.d();
    let cn = c.n();
    let cd = c.d();
    let k = cn * cd;
    assert(k >= 0) by (nonlinear_arith)
        requires
            k == cn * cd,
            cn >= 0,
            cd > 0,
    ;
    assert((an * bd) * k <= (bn * ad) * k) by (nonlinear_arith)
        requires
            an * bd <= bn * ad,
            k >= 0,
    ;
    assert(mul_n(a, c) == an * cn);
    assert(prod_d(b, c) == bd * cd);
    assert(mul_n(b, c) == bn * cn);
    assert(prod_d(a, c) == ad * cd);
    assert((an * cn) * (bd * cd) == (an * bd) * k) by (nonlinear_arith)
        requires
            k == cn * cd,
    ;
    assert((bn * cn) * (ad * cd) == (bn * ad) * k) by (nonlinear_arith)
        requires
            k == cn * cd,
    ;
}

/// **Squares are non-negative, and vanish only at zero**: the exact square
/// `a · a` has a non-negative numerator, zero exactly when `a` is zero.
///
/// This is the remaining ordered-field axiom after translation and scaling
/// compatibility. The "only at zero" half carries the field-theoretic content.
/// The square of a nonzero element is strictly positive. Sum-of-squares
/// magnitudes, such as `hypot`'s `x·x + y·y`, are therefore definite rather
/// than merely non-negative.
pub proof fn theorem_square_sign(a: Rat)
    requires
        a.wf(),
    ensures
        mul_n(a, a) >= 0,
        mul_n(a, a) == 0 <==> a.n() == 0,
        prod_d(a, a) > 0,
{
    assert(a.n() * a.n() >= 0) by (nonlinear_arith);
    if a.n() != 0 {
        assert(a.n() * a.n() != 0) by (nonlinear_arith)
            requires
                a.n() != 0,
        ;
    }
    assert(a.d() * a.d() > 0) by (nonlinear_arith)
        requires
            a.d() > 0,
    ;
}

/// **Reciprocal reverses the order on positives**: for `0 < a <= b`,
/// `1/b <= 1/a`. Both reciprocals are themselves positive.
///
/// The statement uses [`q_is_recip`], the division-free relation that
/// [`theorem_recip_involution`] also uses. It therefore applies to the output of
/// `Rat::recip`. Division-based bounds reduce to this monotonicity fact: a
/// larger denominator gives a smaller quotient. The positivity hypotheses are
/// necessary. On mixed signs the conclusion is false.
pub proof fn theorem_recip_antitone(a: Rat, b: Rat, ra: Rat, rb: Rat)
    requires
        a.wf(),
        b.wf(),
        ra.wf(),
        rb.wf(),
        a.n() > 0,
        b.n() > 0,
        q_le(a, b),
        crate::q::q_is_recip(ra, a),
        crate::q::q_is_recip(rb, b),
    ensures
        ra.n() > 0,
        rb.n() > 0,
        q_le(rb, ra),
{
    // The reciprocal of a positive value is positive: ra.n·a.n equals the
    // positive a.d·ra.d, and a.n > 0.
    assert(ra.n() > 0) by (nonlinear_arith)
        requires
            ra.n() * a.n() == a.d() * ra.d(),
            a.n() > 0,
            a.d() > 0,
            ra.d() > 0,
    ;
    assert(rb.n() > 0) by (nonlinear_arith)
        requires
            rb.n() * b.n() == b.d() * rb.d(),
            b.n() > 0,
            b.d() > 0,
            rb.d() > 0,
    ;
    let p = a.n() * b.n();
    assert(p > 0) by (nonlinear_arith)
        requires
            p == a.n() * b.n(),
            a.n() > 0,
            b.n() > 0,
    ;
    assert(ra.d() * rb.d() > 0) by (nonlinear_arith)
        requires
            ra.d() > 0,
            rb.d() > 0,
    ;
    // Scale the goal by the positive p == a.n·b.n and substitute both
    // reciprocal relations. What remains is the hypothesis a <= b, scaled by
    // the positive ra.d·rb.d. Each step is a small ring identity or a
    // congruence.
    assert((rb.n() * ra.d()) * p == (rb.n() * b.n()) * (a.n() * ra.d())) by (nonlinear_arith)
        requires
            p == a.n() * b.n(),
    ;
    assert((rb.n() * b.n()) * (a.n() * ra.d()) == (b.d() * rb.d()) * (a.n() * ra.d()));
    assert((b.d() * rb.d()) * (a.n() * ra.d()) == (a.n() * b.d()) * (ra.d() * rb.d()))
        by (nonlinear_arith);
    assert((a.n() * b.d()) * (ra.d() * rb.d()) <= (b.n() * a.d()) * (ra.d() * rb.d()))
        by (nonlinear_arith)
        requires
            a.n() * b.d() <= b.n() * a.d(),
            ra.d() * rb.d() > 0,
    ;
    assert((b.n() * a.d()) * (ra.d() * rb.d()) == (a.d() * ra.d()) * (b.n() * rb.d()))
        by (nonlinear_arith);
    assert((a.d() * ra.d()) * (b.n() * rb.d()) == (ra.n() * a.n()) * (b.n() * rb.d()));
    assert((ra.n() * a.n()) * (b.n() * rb.d()) == (ra.n() * rb.d()) * p) by (nonlinear_arith)
        requires
            p == a.n() * b.n(),
    ;
    assert((rb.n() * ra.d()) * p <= (ra.n() * rb.d()) * p);
    lemma_cancel_pos_le(rb.n() * ra.d(), ra.n() * rb.d(), p);
}

} // verus!
