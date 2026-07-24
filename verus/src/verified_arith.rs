// Proofs under active development (reported non-fatal by ci/verify.sh; promoted
// to the hard gate once green). Self-contained crate root.
//
// This batch: the rest of the comparison surface (le, eq), the order laws
// (antisymmetry, transitivity — V6), abs preservation, and the raw arithmetic
// kernels for add/mul proven overflow-free (V2) and value-correct division-free
// (V3, pre-reduce).

use vstd::prelude::*;

verus! {

pub open spec fn budget() -> int { 4611686018427387903 }        // 2^62 - 1
pub open spec fn i128_max() -> int { 170141183460469231731687303715884105727 }

pub struct Q { pub num: i64, pub den: i64 }

pub open spec fn abs_int(x: int) -> int { if x < 0 { -x } else { x } }

pub open spec fn bounded(q: Q) -> bool {
    &&& q.den >= 1
    &&& -budget() <= q.num as int <= budget()
    &&& q.den as int <= budget()
}

pub open spec fn q_lt(a: Q, b: Q) -> bool {
    (a.num as int) * (b.den as int) < (b.num as int) * (a.den as int)
}
pub open spec fn q_le(a: Q, b: Q) -> bool {
    (a.num as int) * (b.den as int) <= (b.num as int) * (a.den as int)
}
pub open spec fn q_eq(a: Q, b: Q) -> bool {
    (a.num as int) * (b.den as int) == (b.num as int) * (a.den as int)
}

/// V2: `x*y` for budget-bounded `x,y` fits well inside i128.
pub proof fn lemma_prod_bound(x: int, y: int)
    requires -budget() <= x <= budget(), -budget() <= y <= budget(),
    ensures
        -(budget() * budget()) <= x * y <= budget() * budget(),
        budget() * budget() < i128_max(),
{
    assert(-(budget() * budget()) <= x * y <= budget() * budget()) by (nonlinear_arith)
        requires -budget() <= x <= budget(), -budget() <= y <= budget();
    assert(budget() * budget() < i128_max());
}

/// V2+V3: exec `<=` matches the ghost order, no overflow.
pub fn q_le_exec(a: Q, b: Q) -> (r: bool)
    requires bounded(a), bounded(b),
    ensures r == q_le(a, b),
{
    proof {
        lemma_prod_bound(a.num as int, b.den as int);
        lemma_prod_bound(b.num as int, a.den as int);
    }
    let lhs: i128 = (a.num as i128) * (b.den as i128);
    let rhs: i128 = (b.num as i128) * (a.den as i128);
    lhs <= rhs
}

/// V2+V3: exec `==` matches the ghost equality, no overflow.
pub fn q_eq_exec(a: Q, b: Q) -> (r: bool)
    requires bounded(a), bounded(b),
    ensures r == q_eq(a, b),
{
    proof {
        lemma_prod_bound(a.num as int, b.den as int);
        lemma_prod_bound(b.num as int, a.den as int);
    }
    let lhs: i128 = (a.num as i128) * (b.den as i128);
    let rhs: i128 = (b.num as i128) * (a.den as i128);
    lhs == rhs
}

/// V6: the ghost order is antisymmetric (≤ both ways ⟹ equal).
pub proof fn ord_antisymmetric(a: Q, b: Q)
    requires q_le(a, b), q_le(b, a),
    ensures q_eq(a, b),
{
}

/// V6: the ghost order is transitive (positivity of denominators is essential).
pub proof fn ord_transitive(a: Q, b: Q, c: Q)
    requires bounded(a), bounded(b), bounded(c), q_le(a, b), q_le(b, c),
    ensures q_le(a, c),
{
    let an = a.num as int; let ad = a.den as int;
    let bn = b.num as int; let bd = b.den as int;
    let cn = c.num as int; let cd = c.den as int;
    assert(an * cd <= cn * ad) by (nonlinear_arith)
        requires ad >= 1, bd >= 1, cd >= 1, an * bd <= bn * ad, bn * cd <= cn * bd;
}

/// V6/V1: abs preserves the bound.
pub fn abs(q: Q) -> (r: Q)
    requires bounded(q),
    ensures bounded(r), r.num as int == abs_int(q.num as int), r.den == q.den,
{
    Q { num: if q.num < 0 { -q.num } else { q.num }, den: q.den }
}

/// V2+V3 for `add`, pre-reduce: the raw numerator/denominator are overflow-free
/// in i128 and model `a + b` exactly (division-free).
pub fn raw_add(a: Q, b: Q) -> (r: (i128, i128))
    requires bounded(a), bounded(b),
    ensures
        // value correctness: n * (a.den*b.den) == (a.num*b.den + b.num*a.den) * d
        (r.0 as int) == (a.num as int) * (b.den as int) + (b.num as int) * (a.den as int),
        (r.1 as int) == (a.den as int) * (b.den as int),
        r.1 as int >= 1,
{
    proof {
        lemma_prod_bound(a.num as int, b.den as int);
        lemma_prod_bound(b.num as int, a.den as int);
        lemma_prod_bound(a.den as int, b.den as int);
        // sum of two products still far inside i128 (< 2^126).
        assert(2 * (budget() * budget()) < i128_max());
        assert((a.den as int) * (b.den as int) >= 1) by (nonlinear_arith)
            requires a.den as int >= 1, b.den as int >= 1;
    }
    let n: i128 = (a.num as i128) * (b.den as i128) + (b.num as i128) * (a.den as i128);
    let d: i128 = (a.den as i128) * (b.den as i128);
    (n, d)
}

/// V2+V3 for `mul`, pre-reduce.
pub fn raw_mul(a: Q, b: Q) -> (r: (i128, i128))
    requires bounded(a), bounded(b),
    ensures
        (r.0 as int) == (a.num as int) * (b.num as int),
        (r.1 as int) == (a.den as int) * (b.den as int),
        r.1 as int >= 1,
{
    proof {
        lemma_prod_bound(a.num as int, b.num as int);
        lemma_prod_bound(a.den as int, b.den as int);
        assert((a.den as int) * (b.den as int) >= 1) by (nonlinear_arith)
            requires a.den as int >= 1, b.den as int >= 1;
    }
    let n: i128 = (a.num as i128) * (b.num as i128);
    let d: i128 = (a.den as i128) * (b.den as i128);
    (n, d)
}

/// V6: `add` is commutative at the value level — its numerator and denominator
/// are both symmetric in `(a, b)`, so the reduced+rounded results coincide.
pub proof fn raw_add_commutative(a: Q, b: Q)
    ensures
        (a.num as int) * (b.den as int) + (b.num as int) * (a.den as int)
            == (b.num as int) * (a.den as int) + (a.num as int) * (b.den as int),
        (a.den as int) * (b.den as int) == (b.den as int) * (a.den as int),
{
}

/// V6: `mul` is commutative at the value level.
pub proof fn raw_mul_commutative(a: Q, b: Q)
    ensures
        (a.num as int) * (b.num as int) == (b.num as int) * (a.num as int),
        (a.den as int) * (b.den as int) == (b.den as int) * (a.den as int),
{
}

fn main() {}

}
