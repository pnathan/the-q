//! Algebraic laws (obligation V6).
//!
//! # What holds, and what does not
//!
//! | law | status |
//! |---|---|
//! | `a + b == b + a`, `a * b == b * a` | **always**, bit-for-bit |
//! | `(a + b) + c == a + (b + c)` | **only on the exact path** |
//! | `(a * b) * c == a * (b * c)` | **only on the exact path** |
//! | `a * (b + c) == a*b + a*c` | **only on the exact path** |
//! | `Ord` is a total order agreeing with the ghost order | always |
//! | `-(-a) == a`, `abs(abs(a)) == abs(a)`, `1/(1/a) == a` | always |
//!
//! Commutativity survives rounding because both orderings feed *provably equal*
//! integers into the same rounding function. Associativity does not, and this
//! crate does not pretend otherwise: rounding the inner sum first can land on a
//! different grid point than rounding the outer one. The consuming engine's
//! order-independence claims therefore hold **exactly** whenever the whole
//! computation stays inside the budget, and **up to the accumulated error
//! bound** otherwise. See `README.md`.

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
use crate::types::{Dir, Q};

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

/// **Canonicality.** Two well-formed `Q` are mathematically equal exactly when
/// they are structurally equal.
///
/// This is what makes `PartialEq`, `Eq` and `Hash` safe to derive, and what
/// makes every value have exactly one bit pattern — the property that turns
/// "deterministic" from a hope into a fact.
pub proof fn lemma_canonical_eq(a: Q, b: Q)
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
        // `wf` gives gcd(|num|, den) == 1; Euclid's lemma wants the divisor
        // first, so flip both with `lemma_gcd_sym`.
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
// Commutativity — holds unconditionally, rounding and all
// ---------------------------------------------------------------------------

/// **`add` is commutative**, bit-for-bit, rounding included.
///
/// `add_n(a, b)` and `add_n(b, a)` are equal integers and `prod_d` is
/// symmetric, so both calls apply [`round_frac`] to the same arguments.
pub proof fn theorem_add_commutative(a: Q, b: Q, dir: Dir)
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
pub proof fn theorem_mul_commutative(a: Q, b: Q, dir: Dir)
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
/// computation fits the budget, the computation is end-to-end exact — not
/// "accurate to within a bound", *exact*.
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
pub proof fn theorem_add_associative_exact(a: Q, b: Q, c: Q, dir: Dir)
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

/// Two `Q` denoting the same fraction are equal as values.
pub proof fn lemma_same_value_eq(x: Q, y: Q, n: int, d: int)
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
/// Two disciplines make this go through, and both were learned the hard way:
/// a `by (nonlinear_arith)` block sees **only** what its own `requires` lists —
/// it does not inherit the surrounding context — so every step that combines
/// earlier facts is a plain `assert`, and only pure ring identities are handed
/// to the nonlinear tactic. And those identities are kept small by naming
/// subterms, because a five-variable degree-five goal exhausts the budget.
pub proof fn lemma_left_assoc_value(a: Q, b: Q, c: Q, ab: Q, left: Q, sn: int, sd: int)
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
#[verifier::rlimit(20)]
pub proof fn lemma_right_assoc_value(a: Q, b: Q, c: Q, bc: Q, right: Q, sn: int, sd: int)
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
pub proof fn lemma_add_assoc_exact_values(a: Q, b: Q, c: Q, ab: Q, bc: Q, left: Q, right: Q)
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
pub proof fn theorem_mul_associative_exact(a: Q, b: Q, c: Q, ab: Q, bc: Q, left: Q, right: Q)
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
pub proof fn lemma_mul_chain_value(a: Q, b: Q, c: Q, ab: Q, left: Q, pn: int, pd: int)
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
pub proof fn lemma_mul_chain_value_right(a: Q, b: Q, c: Q, bc: Q, right: Q, pn: int, pd: int)
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
    a: Q,
    b: Q,
    c: Q,
    bc: Q,
    lhs: Q,
    ab: Q,
    ac: Q,
    rhs: Q,
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
pub proof fn lemma_distrib_lhs_value(a: Q, b: Q, c: Q, bc: Q, lhs: Q, dn: int, dd: int)
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
pub proof fn lemma_distrib_rhs_value(a: Q, b: Q, c: Q, ab: Q, ac: Q, rhs: Q, dn: int, dd: int)
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
pub proof fn theorem_identities(a: Q, dir: Dir)
    requires
        a.wf(),
    ensures
        ({
            let z = Q { num: 0, den: 1 };
            let o = Q { num: 1, den: 1 };
            &&& exact_path(add_n(a, z), prod_d(a, z))
            &&& exact_path(mul_n(a, o), prod_d(a, o))
            &&& round_frac(add_n(a, z), prod_d(a, z), dir) == a
            &&& round_frac(mul_n(a, o), prod_d(a, o), dir) == a
        }),
{
    let z = Q { num: 0, den: 1 };
    let o = Q { num: 1, den: 1 };
    assert(add_n(a, z) == a.n() && prod_d(a, z) == a.d());
    assert(mul_n(a, o) == a.n() && prod_d(a, o) == a.d());
    crate::round::lemma_r1_identity(a.n(), a.d(), dir);
    lemma_round_of_wf_is_self(a, dir);
}

/// Rounding a value that is already a well-formed `Q` returns it unchanged.
pub proof fn lemma_round_of_wf_is_self(a: Q, dir: Dir)
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
/// Totality is where `Q` beats `f64` outright: there is no `NaN`, so there is
/// no incomparable pair, so `PartialOrd` is never `None`.
pub proof fn theorem_order_total(a: Q, b: Q, c: Q)
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
pub proof fn theorem_neg_abs_involution(a: Q)
    requires
        a.wf(),
    ensures
        ({
            let na = Q { num: (-a.n()) as i64, den: a.den };
            let aa = Q { num: abs_int(a.n()) as i64, den: a.den };
            &&& Q { num: (-(na.n())) as i64, den: na.den } == a
            &&& Q { num: abs_int(aa.n()) as i64, den: aa.den } == aa
        }),
{
}

/// `1/(1/a) == a` for non-zero `a`. Reciprocal is exact in both directions, so
/// this is a genuine involution — no rounding anywhere.
pub proof fn theorem_recip_involution(a: Q, r: Q, rr: Q)
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
pub proof fn theorem_sub_is_add_neg(a: Q, b: Q)
    requires
        a.wf(),
        b.wf(),
    ensures
        ({
            let nb = Q { num: (-b.n()) as i64, den: b.den };
            sub_n(a, b) == add_n(a, nb) && prod_d(a, b) == prod_d(a, nb)
        }),
{
    crate::model::lemma_max_mag_pow2();
    // Pushing the negation through the product is nonlinear.
    assert((-b.n()) * a.d() == -(b.n() * a.d())) by (nonlinear_arith);
}

/// `a / b == a * (1/b)` as exact rationals.
pub proof fn theorem_div_is_mul_recip(a: Q, b: Q, rb: Q)
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

} // verus!
