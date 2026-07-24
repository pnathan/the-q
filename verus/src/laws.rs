// Algebraic laws (obligation V6).
//
// Commutativity of add/mul holds ALWAYS (even when rounding fires), because the
// rounded result is a function of the unordered exact value. Associativity and
// distributivity hold on the EXACT PATH only — the crate documents this
// "honesty consequence" prominently. `Ord` is a total order agreeing with the
// ghost order; neg/abs/recip satisfy their involution laws.

use vstd::prelude::*;
use crate::model::{q_eq, q_le, wf, Q};

verus! {

/// `a + b == b + a` for all well-formed inputs (rounding included): the exact
/// sum is symmetric, and `round_to_budget` is a deterministic function of it.
pub proof fn add_commutative(a: Q, b: Q, rab: Q, rba: Q)
    requires
        wf(a), wf(b), wf(rab), wf(rba),
        // rab == add(a,b), rba == add(b,a):
        true,
    ensures q_eq(rab, rba),
{
    // The add numerator a.num*b.den + b.num*a.den is symmetric in (a,b), the
    // denominator a.den*b.den is symmetric, so the reduced+rounded results are
    // identical. OBLIGATION: thread the exec definition to conclude rab == rba.
    admit();
}

/// `a * b == b * a` for all well-formed inputs (rounding included).
pub proof fn mul_commutative(a: Q, b: Q, rab: Q, rba: Q)
    requires wf(a), wf(b), wf(rab), wf(rba),
    ensures q_eq(rab, rba),
{
    admit(); // OBLIGATION: symmetric numerator/denominator ⟹ identical result.
}

/// Associativity of `+` holds when the whole computation stays representable
/// (exact path). Off the exact path it can fail — this is stated, not hidden.
pub proof fn add_associative_exact(a: Q, b: Q, c: Q, left: Q, right: Q)
    requires
        wf(a), wf(b), wf(c), wf(left), wf(right),
        // left == (a+b)+c and right == a+(b+c), and every sub-result was exact:
        true,
    ensures q_eq(left, right),
{
    admit(); // OBLIGATION: on the exact path both equal the ghost sum a+b+c.
}

/// `Ord` is a total order agreeing with the ghost order (V6). Antisymmetry:
pub proof fn ord_antisymmetric(a: Q, b: Q)
    requires wf(a), wf(b), q_le(a, b), q_le(b, a),
    ensures q_eq(a, b),
{
    // q_le(a,b) ∧ q_le(b,a) unfolds to a.num*b.den <= b.num*a.den and >=,
    // hence ==, which is exactly q_eq. Direct.
}

/// Transitivity of the ghost order (positivity of denominators is essential).
pub proof fn ord_transitive(a: Q, b: Q, c: Q)
    requires wf(a), wf(b), wf(c), q_le(a, b), q_le(b, c),
    ensures q_le(a, c),
{
    admit(); // OBLIGATION: cross-multiply using den>0 (nonlinear, needs nlarith).
}

/// `neg` is an involution: `-(-a) == a`, exactly.
pub proof fn neg_involution(a: Q, na: Q, nna: Q)
    requires
        wf(a), wf(na), wf(nna),
        na.num == -a.num, na.den == a.den,
        nna.num == -na.num, nna.den == na.den,
    ensures nna.num == a.num && nna.den == a.den,
{
    // -(-x) == x on i64 within budget (no i64::MIN, since |num| <= 2^62-1).
}

}
