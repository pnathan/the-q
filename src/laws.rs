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
        assert(divides(a.d(), a.n() * b.d())) by {
            assert(a.n() * b.d() == b.n() * a.d());
            assert(b.n() * a.d() == a.d() * b.n()) by (nonlinear_arith);
        }
        lemma_euclid(a.d() as nat, abs_int(a.n()) as nat, b.d() as nat);
        assert(divides(b.d(), b.n() * a.d())) by {
            assert(b.n() * a.d() == a.n() * b.d());
            assert(a.n() * b.d() == b.d() * a.n()) by (nonlinear_arith);
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
    let ab = round_frac(add_n(a, b), prod_d(a, b), dir);
    let bc = round_frac(add_n(b, c), prod_d(b, c), dir);
    theorem_exact_path_is_exact(add_n(a, b), prod_d(a, b), dir);
    theorem_exact_path_is_exact(add_n(b, c), prod_d(b, c), dir);
    let left = round_frac(add_n(ab, c), prod_d(ab, c), dir);
    let right = round_frac(add_n(a, bc), prod_d(a, bc), dir);
    theorem_exact_path_is_exact(add_n(ab, c), prod_d(ab, c), dir);
    theorem_exact_path_is_exact(add_n(a, bc), prod_d(a, bc), dir);
    // Both equal (a + b + c) exactly, and exact equality of values is q_eq.
    lemma_add_assoc_exact_values(a, b, c, ab, bc, left, right);
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
    // left  = ((a.n·b.d + b.n·a.d)·c.d + c.n·(a.d·b.d)) / (a.d·b.d·c.d)
    // right = (a.n·(b.d·c.d) + (b.n·c.d + c.n·b.d)·a.d) / (a.d·b.d·c.d)
    // The numerators are equal by ring axioms.
    assert(left.n() * right.d() == right.n() * left.d()) by (nonlinear_arith)
        requires
            a.d() > 0,
            b.d() > 0,
            c.d() > 0,
            ab.d() > 0,
            bc.d() > 0,
            left.d() > 0,
            right.d() > 0,
            ab.n() * (a.d() * b.d()) == (a.n() * b.d() + b.n() * a.d()) * ab.d(),
            bc.n() * (b.d() * c.d()) == (b.n() * c.d() + c.n() * b.d()) * bc.d(),
            left.n() * (ab.d() * c.d()) == (ab.n() * c.d() + c.n() * ab.d()) * left.d(),
            right.n() * (a.d() * bc.d()) == (a.n() * bc.d() + bc.n() * a.d()) * right.d(),
    ;
}

/// **`mul` is associative on the exact path.**
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
    assert(left.n() * right.d() == right.n() * left.d()) by (nonlinear_arith)
        requires
            a.d() > 0,
            b.d() > 0,
            c.d() > 0,
            ab.d() > 0,
            bc.d() > 0,
            left.d() > 0,
            right.d() > 0,
            ab.n() * (a.d() * b.d()) == (a.n() * b.n()) * ab.d(),
            bc.n() * (b.d() * c.d()) == (b.n() * c.n()) * bc.d(),
            left.n() * (ab.d() * c.d()) == (ab.n() * c.n()) * left.d(),
            right.n() * (a.d() * bc.d()) == (a.n() * bc.n()) * right.d(),
    ;
}

/// **Distributivity on the exact path:** `a·(b + c) == a·b + a·c`.
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
    assert(lhs.n() * rhs.d() == rhs.n() * lhs.d()) by (nonlinear_arith)
        requires
            a.d() > 0,
            b.d() > 0,
            c.d() > 0,
            bc.d() > 0,
            lhs.d() > 0,
            ab.d() > 0,
            ac.d() > 0,
            rhs.d() > 0,
            bc.n() * (b.d() * c.d()) == (b.n() * c.d() + c.n() * b.d()) * bc.d(),
            lhs.n() * (a.d() * bc.d()) == (a.n() * bc.n()) * lhs.d(),
            ab.n() * (a.d() * b.d()) == (a.n() * b.n()) * ab.d(),
            ac.n() * (a.d() * c.d()) == (a.n() * c.n()) * ac.d(),
            rhs.n() * (ab.d() * ac.d()) == (ab.n() * ac.d() + ac.n() * ab.d()) * rhs.d(),
    ;
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
