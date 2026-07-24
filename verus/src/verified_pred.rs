// Under development (reported non-fatal). Batch: exec predicates and min/max
// proven to match the ghost model (V3), plus reflexivity of the order (V6).

use vstd::prelude::*;

verus! {

pub open spec fn budget() -> int { 4611686018427387903 }

pub struct Q { pub num: i64, pub den: i64 }

pub open spec fn bounded(q: Q) -> bool {
    &&& q.den >= 1
    &&& -budget() <= q.num as int <= budget()
    &&& q.den as int <= budget()
}

pub open spec fn i128_max() -> int { 170141183460469231731687303715884105727 }

pub open spec fn q_le(a: Q, b: Q) -> bool {
    (a.num as int) * (b.den as int) <= (b.num as int) * (a.den as int)
}

/// V2: budget-bounded products fit i128.
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

/// V6: the ghost order is reflexive.
pub proof fn q_le_reflexive(a: Q)
    ensures q_le(a, a),
{
}

/// V3: `is_zero` matches the ghost predicate `value == 0`.
pub fn is_zero(q: Q) -> (r: bool)
    requires bounded(q),
    ensures r == (q.num as int == 0),
{
    q.num == 0
}

/// V3: `signum` matches the sign of the value (denominator is positive).
pub fn signum(q: Q) -> (r: i32)
    requires bounded(q),
    ensures
        (q.num as int) > 0 ==> r == 1,
        (q.num as int) == 0 ==> r == 0,
        (q.num as int) < 0 ==> r == -1,
{
    if q.num > 0 {
        1
    } else if q.num == 0 {
        0
    } else {
        -1
    }
}

/// V3: `in_unit_interval` matches `0 <= value <= 1` (division-free).
pub fn in_unit_interval(q: Q) -> (r: bool)
    requires bounded(q),
    ensures r == (0 <= q.num as int && q.num as int <= q.den as int),
{
    0 <= q.num && q.num <= q.den
}

/// V3: `min` returns one of its arguments and is `<=` both.
pub fn min(a: Q, b: Q) -> (r: Q)
    requires bounded(a), bounded(b),
    ensures
        r == a || r == b,
        q_le(r, a),
        q_le(r, b),
{
    proof {
        q_le_reflexive(a);
        q_le_reflexive(b);
        lemma_prod_bound(a.num as int, b.den as int);
        lemma_prod_bound(b.num as int, a.den as int);
    }
    // a <= b  ⟺  a.num*b.den <= b.num*a.den, computed overflow-free in i128.
    let le = (a.num as i128) * (b.den as i128) <= (b.num as i128) * (a.den as i128);
    if le {
        a
    } else {
        b
    }
}

/// V3: `max` returns one of its arguments and is `>=` both.
pub fn max(a: Q, b: Q) -> (r: Q)
    requires bounded(a), bounded(b),
    ensures
        r == a || r == b,
        q_le(a, r),
        q_le(b, r),
{
    proof {
        q_le_reflexive(a);
        q_le_reflexive(b);
        lemma_prod_bound(a.num as int, b.den as int);
        lemma_prod_bound(b.num as int, a.den as int);
    }
    let le = (a.num as i128) * (b.den as i128) <= (b.num as i128) * (a.den as i128);
    if le {
        b
    } else {
        a
    }
}

fn main() {}

}
