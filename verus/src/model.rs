// Ghost model and invariants (obligations V1, V3-specs).
//
// The verified region reasons about `Q` through an unbounded-integer ghost
// model. Value correctness is stated *division-free*, by cross-multiplication,
// to keep z3 stable (this mirrors the Lean discipline of the parent research
// program). No `spec` here uses SMT division on the modelled values.

use vstd::prelude::*;

verus! {

/// The mirror of the executable `Q { num: i64, den: i64 }`.
pub struct Q {
    pub num: i64,
    pub den: i64,
}

/// `2^62 - 1`, the width budget (I2).
pub open spec fn budget() -> int { (1int << 62) - 1 }

/// Greatest common divisor of two naturals (structural recursion; total).
pub open spec fn spec_gcd(a: nat, b: nat) -> nat
    decreases b
{
    if b == 0 { a } else { spec_gcd(b, (a % b) as nat) }
}

/// `d` divides `n`.
pub open spec fn divides(d: int, n: int) -> bool {
    exists|k: int| n == d * k
}

/// **I1 (canonical)**: positive reduced denominator, zero normalized to 0/1.
pub open spec fn canonical(q: Q) -> bool {
    &&& q.den > 0
    &&& spec_gcd(abs_int(q.num as int) as nat, q.den as nat) == 1
    &&& (q.num == 0 ==> q.den == 1)
}

/// **I2 (bounded)**: numerator magnitude and denominator within the budget.
pub open spec fn bounded(q: Q) -> bool {
    &&& abs_int(q.num as int) <= budget()
    &&& (q.den as int) <= budget()
}

/// Well-formed = I1 ∧ I2. Every public op `requires` and `ensures` this (V1).
pub open spec fn wf(q: Q) -> bool {
    canonical(q) && bounded(q)
}

/// Absolute value on ghost `int`.
pub open spec fn abs_int(x: int) -> int { if x < 0 { -x } else { x } }

/// The exact rational value of `q`, as the pair `(num, den)` — we never form the
/// SMT quotient. Relations below compare these pairs by cross-multiplication.
pub open spec fn q_num(q: Q) -> int { q.num as int }
pub open spec fn q_den(q: Q) -> int { q.den as int }

/// Value equality (division-free): `a == b`  ⟺  `a.num·b.den == b.num·a.den`.
pub open spec fn q_eq(a: Q, b: Q) -> bool {
    q_num(a) * q_den(b) == q_num(b) * q_den(a)
}

/// Value order (division-free), valid because both denominators are positive.
pub open spec fn q_le(a: Q, b: Q) -> bool {
    q_num(a) * q_den(b) <= q_num(b) * q_den(a)
}

pub open spec fn q_lt(a: Q, b: Q) -> bool {
    q_num(a) * q_den(b) < q_num(b) * q_den(a)
}

/// The exact value of "a + b" as a raw (unreduced) fraction, for stating the
/// value-correctness `ensures` of `add` division-free:
///   r  ==  a + b   ⟺   r.num·(a.den·b.den) == (a.num·b.den + b.num·a.den)·r.den
pub open spec fn is_sum(r: Q, a: Q, b: Q) -> bool {
    q_num(r) * (q_den(a) * q_den(b))
        == (q_num(a) * q_den(b) + q_num(b) * q_den(a)) * q_den(r)
}

pub open spec fn is_prod(r: Q, a: Q, b: Q) -> bool {
    q_num(r) * (q_den(a) * q_den(b)) == (q_num(a) * q_num(b)) * q_den(r)
}

/// Since canonical form is unique, value equality is *structural* equality.
/// (V3 corollary — enables the derived `PartialEq`/`Hash`/`Eq`.)
pub proof fn lemma_canonical_eq_is_structural(a: Q, b: Q)
    requires wf(a), wf(b), q_eq(a, b),
    ensures a.num == b.num && a.den == b.den,
{
    // OBLIGATION: uniqueness of canonical form. Standard number-theory argument:
    // from q_eq and coprimality of both (num,den) pairs, a.den | b.den and
    // b.den | a.den (both positive) ⟹ a.den == b.den ⟹ a.num == b.num.
    // Requires `lemma_gcd_divides` (gcd.rs) + the coprime-cross-multiply lemma.
    admit();
}

}
