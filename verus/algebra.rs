// V6: algebraic laws -- commutativity (always), associativity/
// distributivity (on the exact path), neg/recip involutions, abs
// idempotence.
//
// Standalone Verus proof file mirroring the formulas in `src/ops.rs`.
// Checked directly via `verus verus/algebra.rs`; see verus/smoke_test.rs's
// header comment for why these live outside the cargo package.
//
// Scope note on why proving the *exact-formula* identities below is
// actually sufficient for the shipped `Q::add`/`Q::mul` (not just a
// structural analogue): the shipped pipeline is
// `canonicalize_i128(exact) -> round_to_budget(...)`, a pure, deterministic
// function of the exact `(num, den)` pair. When two computations produce
// *identical* exact pairs (not merely equal rational values -- literally
// equal `(int, int)`), the deterministic pipeline downstream necessarily
// produces identical output, with no separate argument needed. That's
// exactly what commutativity/associativity/distributivity are proved at
// below: the exact-formula pairs are shown to be literally equal (for
// commutativity, denominators too; for associativity/distributivity, via
// value-equality `q_value_eq` since the denominators differ syntactically
// but represent the same rational).
//
// Authored and iterated on entirely via CI feedback -- no local Verus
// available (see TRUSTED.md).

use vstd::prelude::*;

verus! {

/// Two exact `(num, den)` pairs (`den > 0`) represent the same rational,
/// via cross-multiplication -- the division-free ghost-model equality
/// relation used throughout (spec's "division-free cross-multiplication"
/// discipline).
pub open spec fn q_value_eq(n1: int, d1: int, n2: int, d2: int) -> bool {
    n1 * d2 == n2 * d1
}

pub open spec fn add_num(n1: int, d1: int, n2: int, d2: int) -> int {
    n1 * d2 + n2 * d1
}

pub open spec fn add_den(d1: int, d2: int) -> int {
    d1 * d2
}

pub open spec fn mul_num(n1: int, n2: int) -> int {
    n1 * n2
}

pub open spec fn mul_den(d1: int, d2: int) -> int {
    d1 * d2
}

// --- Commutativity (always, per spec: "add/mul commutative (always)") ---

proof fn lemma_add_commutative(n1: int, d1: int, n2: int, d2: int)
    ensures
        add_num(n1, d1, n2, d2) == add_num(n2, d2, n1, d1),
        add_den(d1, d2) == add_den(d2, d1),
{
}

proof fn lemma_mul_commutative(n1: int, d1: int, n2: int, d2: int)
    ensures
        mul_num(n1, n2) == mul_num(n2, n1),
        mul_den(d1, d2) == mul_den(d2, d1),
{
}

// --- Associativity/distributivity, exact path only ---

/// `(a+b)+c` and `a+(b+c)` have *syntactically identical* denominators
/// (`da*db*dc` either way, by associativity of `*`), so value-equality
/// reduces to the numerators being literally equal -- a pure polynomial
/// identity (each side expands to the same three degree-3 monomials).
proof fn lemma_add_associative(na: int, da: int, nb: int, db: int, nc: int, dc: int)
    requires
        da > 0,
        db > 0,
        dc > 0,
    ensures
        q_value_eq(
            add_num(add_num(na, da, nb, db), add_den(da, db), nc, dc),
            add_den(add_den(da, db), dc),
            add_num(na, da, add_num(nb, db, nc, dc), add_den(db, dc)),
            add_den(da, add_den(db, dc)),
        ),
{
    assert(add_den(add_den(da, db), dc) == add_den(da, add_den(db, dc))) by (nonlinear_arith)
    {}
    assert(add_num(add_num(na, da, nb, db), add_den(da, db), nc, dc) == add_num(
        na,
        da,
        add_num(nb, db, nc, dc),
        add_den(db, dc),
    )) by (nonlinear_arith)
    {}
}

/// `a*(b+c)` and `a*b + a*c`: same shape of argument -- the denominators
/// are syntactically identical (`da*(db*dc)` vs `(da*db)*(da*dc)`... note
/// these are NOT syntactically identical for mul-distributes-over-add
/// (the RHS denominator has an extra `da` factor), so this one genuinely
/// needs the cross-multiplication value-equality, not just a numerator
/// match.
proof fn lemma_mul_distributes_over_add(na: int, da: int, nb: int, db: int, nc: int, dc: int)
    requires
        da > 0,
        db > 0,
        dc > 0,
    ensures
        q_value_eq(
            mul_num(na, add_num(nb, db, nc, dc)),
            mul_den(da, add_den(db, dc)),
            add_num(mul_num(na, nb), mul_den(da, db), mul_num(na, nc), mul_den(da, dc)),
            add_den(mul_den(da, db), mul_den(da, dc)),
        ),
{
    // Both sides of the cross-multiplication equal the same expanded
    // polynomial (na*nb*da*da*db*dc*dc + na*nc*da*da*db*db*dc) -- proved
    // as two separate, smaller nonlinear_arith goals rather than one
    // combined identity, since the combined form timed out (rlimit
    // exceeded) even at a raised budget. Each half is still a real
    // algebraic expansion, just with half the bridging work per query.
    let lhs = mul_num(na, add_num(nb, db, nc, dc)) * add_den(mul_den(da, db), mul_den(da, dc));
    let rhs = add_num(mul_num(na, nb), mul_den(da, db), mul_num(na, nc), mul_den(da, dc)) * mul_den(
        da,
        add_den(db, dc),
    );
    let canonical = na * nb * da * da * db * dc * dc + na * nc * da * da * db * db * dc;
    assert(lhs == canonical) by (nonlinear_arith)
    {}
    assert(rhs == canonical) by (nonlinear_arith)
    {}
}

// --- Involutions / idempotence ---

proof fn lemma_neg_involution(n: int)
    ensures
        -(-n) == n,
{
}

/// `recip`'s numerator half: `n > 0 -> d`, else `-d`.
pub open spec fn recip_num(n: int, d: int) -> int {
    if n > 0 {
        d
    } else {
        -d
    }
}

/// `recip`'s denominator half: `n > 0 -> n`, else `-n`.
pub open spec fn recip_den(n: int, d: int) -> int {
    if n > 0 {
        n
    } else {
        -n
    }
}

pub open spec fn abs_spec(n: int) -> int {
    if n < 0 {
        -n
    } else {
        n
    }
}

/// `recip` swaps `(num, den)` (with a sign fixup so `den` stays positive);
/// swapping twice returns the original pair exactly -- not just an
/// equivalent value.
proof fn lemma_recip_involution(n: int, d: int)
    requires
        n != 0,
        d > 0,
    ensures
        recip_num(recip_num(n, d), recip_den(n, d)) == n,
        recip_den(recip_num(n, d), recip_den(n, d)) == d,
{
}

proof fn lemma_abs_idempotent(n: int)
    ensures
        abs_spec(abs_spec(n)) == abs_spec(n),
{
}

fn main() {}

} // verus!
