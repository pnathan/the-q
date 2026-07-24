//! Algebraic laws (obligation V6).
//!
//! - `add`/`mul` are **commutative always** (with or without rounding):
//!   the exact fractions coincide, and `round_char` pins the result.
//! - Associativity and distributivity hold **on the exact path** (R1):
//!   whenever the intermediate results are exact, the two evaluation
//!   orders produce structurally identical values. With rounding they
//!   hold only up to the R3 bound - documented, not papered over.
//! - Involution laws for `neg` and `recip`.

use vstd::prelude::*;

#[allow(unused_imports)]
use crate::arith::*;
#[allow(unused_imports)]
use crate::q::*;
#[allow(unused_imports)]
use crate::round::*;
#[allow(unused_imports)]
use crate::specs::*;

verus! {

// ---------------------------------------------------------------------------
// The exactness theorem (R1, restated as the headline consequence)
// ---------------------------------------------------------------------------

/// If the exact reduced result fits the budget, the op returned it
/// *exactly* - so any computation whose exact intermediate values all fit
/// the budget is end-to-end exact.
pub proof fn theorem_exact_path(r: Q, en: int, ed: int, dir: Dir)
    requires
        ed > 0,
        r.inv(),
        round_char(r, en, ed, dir),
        new_fits(en, ed),
    ensures
        r.is_frac(en, ed),
{
}

/// On the exact path the result does not depend on the rounding direction.
pub proof fn theorem_exact_dir_independent(r1: Q, r2: Q, en: int, ed: int, dir1: Dir, dir2: Dir)
    requires
        ed > 0,
        r1.inv(),
        r2.inv(),
        round_char(r1, en, ed, dir1),
        round_char(r2, en, ed, dir2),
        new_fits(en, ed),
    ensures
        r1 == r2,
{
    assert(r1.num_s() * r2.den_s() == r2.num_s() * r1.den_s()) by (nonlinear_arith)
        requires
            r1.num_s() * ed == en * r1.den_s(),
            r2.num_s() * ed == en * r2.den_s(),
            ed > 0;
    lemma_canonical_unique(r1, r2);
}

// ---------------------------------------------------------------------------
// Commutativity (always, rounding included)
// ---------------------------------------------------------------------------

/// `a + b == b + a`, bit-exactly, in every rounding mode.
pub proof fn theorem_add_comm(a: Q, b: Q, r1: Q, r2: Q, dir: Dir)
    requires
        a.inv(),
        b.inv(),
        r1.inv(),
        r2.inv(),
        round_char(r1, add_en(a, b), dd_ed(a, b), dir),
        round_char(r2, add_en(b, a), dd_ed(b, a), dir),
    ensures
        r1 == r2,
{
    assert(a.den_s() * b.den_s() == b.den_s() * a.den_s()) by (nonlinear_arith);
    assert(add_en(a, b) == add_en(b, a));
    assert(dd_ed(a, b) == dd_ed(b, a));
    assert(dd_ed(a, b) > 0) by (nonlinear_arith)
        requires a.den_s() > 0, b.den_s() > 0;
    lemma_round_char_unique(r1, r2, add_en(a, b), dd_ed(a, b), dir);
}

/// `a * b == b * a`, bit-exactly, in every rounding mode.
pub proof fn theorem_mul_comm(a: Q, b: Q, r1: Q, r2: Q, dir: Dir)
    requires
        a.inv(),
        b.inv(),
        r1.inv(),
        r2.inv(),
        round_char(r1, mul_en(a, b), dd_ed(a, b), dir),
        round_char(r2, mul_en(b, a), dd_ed(b, a), dir),
    ensures
        r1 == r2,
{
    assert(a.num_s() * b.num_s() == b.num_s() * a.num_s()) by (nonlinear_arith);
    assert(a.den_s() * b.den_s() == b.den_s() * a.den_s()) by (nonlinear_arith);
    assert(mul_en(a, b) == mul_en(b, a));
    assert(dd_ed(a, b) == dd_ed(b, a));
    assert(dd_ed(a, b) > 0) by (nonlinear_arith)
        requires a.den_s() > 0, b.den_s() > 0;
    lemma_round_char_unique(r1, r2, mul_en(a, b), dd_ed(a, b), dir);
}

// ---------------------------------------------------------------------------
// Exact-path associativity of addition
// ---------------------------------------------------------------------------

/// Fraction-elimination step: if `x == mn/md + n3/d3` (cross-multiplied)
/// and `mn/md == e/dd`, then `x == (e*d3 + n3*dd)/(dd*d3)`.
proof fn lemma_elim_middle(xn: int, xd: int, mn: int, md: int, e: int, dd: int, n3: int, d3: int)
    requires
        md > 0,
        xn * (md * d3) == (mn * d3 + n3 * md) * xd,
        mn * dd == e * md,
    ensures
        xn * (dd * d3) == (e * d3 + n3 * dd) * xd,
{
    let lhs1 = xn * (md * d3);
    let rhs1 = (mn * d3 + n3 * md) * xd;
    // multiply both sides by dd (congruence), then renormalize each side
    assert(lhs1 * dd == rhs1 * dd);
    assert(lhs1 * dd == (xn * (dd * d3)) * md) by (nonlinear_arith)
        requires lhs1 == xn * (md * d3);
    assert(rhs1 * dd == (mn * dd) * (d3 * xd) + ((n3 * md) * xd) * dd) by (nonlinear_arith)
        requires rhs1 == (mn * d3 + n3 * md) * xd;
    assert((mn * dd) * (d3 * xd) == (e * md) * (d3 * xd));
    assert((e * md) * (d3 * xd) + ((n3 * md) * xd) * dd == ((e * d3 + n3 * dd) * xd) * md) by {
        broadcast use vstd::arithmetic::mul::group_mul_properties;
    };
    assert((xn * (dd * d3)) * md == ((e * d3 + n3 * dd) * xd) * md);
    lemma_cancel_pos(xn * (dd * d3), (e * d3 + n3 * dd) * xd, md);
}

/// Cancel a positive factor: `a*c == b*c`, `c > 0` implies `a == b`.
proof fn lemma_cancel_pos(a: int, b: int, c: int)
    requires
        a * c == b * c,
        c > 0,
    ensures
        a == b,
{
    assert(a == b) by (nonlinear_arith)
        requires a * c == b * c, c > 0;
}

/// `(a + b) + c == a + (b + c)` when both inner sums and both outer sums
/// are exact (the R1 path). With rounding, associativity holds only up to
/// the accumulated R3 bound - see the crate README.
pub proof fn theorem_add_assoc_exact(a: Q, b: Q, c: Q, ab: Q, bc: Q, l: Q, r: Q)
    requires
        a.inv(),
        b.inv(),
        c.inv(),
        ab.inv(),
        bc.inv(),
        l.inv(),
        r.inv(),
        ab.is_frac(add_en(a, b), dd_ed(a, b)),
        bc.is_frac(add_en(b, c), dd_ed(b, c)),
        l.is_frac(add_en(ab, c), dd_ed(ab, c)),
        r.is_frac(add_en(a, bc), dd_ed(a, bc)),
    ensures
        l == r,
{
    let na = a.num_s();
    let da = a.den_s();
    let nb = b.num_s();
    let db = b.den_s();
    let nc = c.num_s();
    let dc = c.den_s();

    // Eliminate ab from l's relation.
    // l.is_frac(add_en(ab,c), dd_ed(ab,c)):
    //   l.num * (ab.den * dc) == (ab.num * dc + nc * ab.den) * l.den
    lemma_elim_middle(
        l.num_s(), l.den_s(),
        ab.num_s(), ab.den_s(),
        na * db + nb * da, da * db,
        nc, dc,
    );
    // => l.num * ((da*db) * dc) == ((na*db + nb*da) * dc + nc * (da*db)) * l.den

    // Eliminate bc from r's relation; first commute the products so the
    // middle term appears on the left of the sum.
    assert(r.num_s() * (bc.den_s() * da) == (bc.num_s() * da + na * bc.den_s()) * r.den_s())
        by (nonlinear_arith)
        requires
            r.num_s() * (da * bc.den_s()) == (na * bc.den_s() + bc.num_s() * da) * r.den_s();
    lemma_elim_middle(
        r.num_s(), r.den_s(),
        bc.num_s(), bc.den_s(),
        nb * dc + nc * db, db * dc,
        na, da,
    );
    // => r.num * ((db*dc) * da) == ((nb*dc + nc*db) * da + na * (db*dc)) * r.den

    // Both sides now sit over the same 3-way denominator; conclude q_eq.
    let big = (na * db + nb * da) * dc + nc * (da * db);
    assert((nb * dc + nc * db) * da + na * (db * dc) == big) by {
        broadcast use vstd::arithmetic::mul::group_mul_properties;
    };
    assert((db * dc) * da == (da * db) * dc) by {
        broadcast use vstd::arithmetic::mul::group_mul_properties;
    };
    let dend = (da * db) * dc;
    assert(dend > 0) by (nonlinear_arith)
        requires da > 0, db > 0, dc > 0, dend == (da * db) * dc;
    lemma_common_value_qeq(l.num_s(), l.den_s(), r.num_s(), r.den_s(), big, dend);
    lemma_canonical_unique(l, r);
}

/// Two fractions equal to the same `big/dend` (`dend > 0`) are q-equal.
proof fn lemma_common_value_qeq(ln: int, ld: int, rn: int, rd: int, big: int, dend: int)
    requires
        dend > 0,
        ln * dend == big * ld,
        rn * dend == big * rd,
    ensures
        ln * rd == rn * ld,
{
    assert((ln * dend) * rd == (big * ld) * rd);
    assert((rn * dend) * ld == (big * rd) * ld);
    assert((ln * dend) * rd == (ln * rd) * dend) by (nonlinear_arith);
    assert((rn * dend) * ld == (rn * ld) * dend) by (nonlinear_arith);
    assert((big * ld) * rd == (big * rd) * ld) by (nonlinear_arith);
    assert((ln * rd) * dend == (rn * ld) * dend);
    lemma_cancel_pos(ln * rd, rn * ld, dend);
}

// ---------------------------------------------------------------------------
// Exact-path associativity of multiplication
// ---------------------------------------------------------------------------

/// `(a * b) * c == a * (b * c)` on the exact path.
pub proof fn theorem_mul_assoc_exact(a: Q, b: Q, c: Q, ab: Q, bc: Q, l: Q, r: Q)
    requires
        a.inv(),
        b.inv(),
        c.inv(),
        ab.inv(),
        bc.inv(),
        l.inv(),
        r.inv(),
        ab.is_frac(mul_en(a, b), dd_ed(a, b)),
        bc.is_frac(mul_en(b, c), dd_ed(b, c)),
        l.is_frac(mul_en(ab, c), dd_ed(ab, c)),
        r.is_frac(mul_en(a, bc), dd_ed(a, bc)),
    ensures
        l == r,
{
    let na = a.num_s();
    let da = a.den_s();
    let nb = b.num_s();
    let db = b.den_s();
    let nc = c.num_s();
    let dc = c.den_s();
    let big = (na * nb) * nc;
    let dend = (da * db) * dc;

    // l-side: eliminate ab.
    // H1: l.num * (ab.den * dc) == (ab.num * nc) * l.den
    // H2: ab.num * (da * db) == (na * nb) * ab.den
    let h1l = l.num_s() * (ab.den_s() * dc);
    let h1r = (ab.num_s() * nc) * l.den_s();
    assert(h1l * (da * db) == h1r * (da * db));
    assert(h1l * (da * db) == (l.num_s() * dend) * ab.den_s()) by (nonlinear_arith)
        requires h1l == l.num_s() * (ab.den_s() * dc), dend == (da * db) * dc;
    assert(h1r * (da * db) == ((ab.num_s() * (da * db)) * nc) * l.den_s()) by (nonlinear_arith)
        requires h1r == (ab.num_s() * nc) * l.den_s();
    assert(((ab.num_s() * (da * db)) * nc) * l.den_s() == (((na * nb) * ab.den_s()) * nc) * l.den_s());
    assert((((na * nb) * ab.den_s()) * nc) * l.den_s() == (big * l.den_s()) * ab.den_s())
        by (nonlinear_arith)
        requires big == (na * nb) * nc;
    assert((l.num_s() * dend) * ab.den_s() == (big * l.den_s()) * ab.den_s());
    lemma_cancel_pos(l.num_s() * dend, big * l.den_s(), ab.den_s());

    // r-side: eliminate bc.
    // H3: r.num * (da * bc.den) == (na * bc.num) * r.den
    // H4: bc.num * (db * dc) == (nb * nc) * bc.den
    let h3l = r.num_s() * (da * bc.den_s());
    let h3r = (na * bc.num_s()) * r.den_s();
    assert(h3l * (db * dc) == h3r * (db * dc));
    assert(h3l * (db * dc) == (r.num_s() * dend) * bc.den_s()) by (nonlinear_arith)
        requires h3l == r.num_s() * (da * bc.den_s()), dend == (da * db) * dc;
    assert(h3r * (db * dc) == (na * (bc.num_s() * (db * dc))) * r.den_s()) by (nonlinear_arith)
        requires h3r == (na * bc.num_s()) * r.den_s();
    assert((na * (bc.num_s() * (db * dc))) * r.den_s() == (na * ((nb * nc) * bc.den_s())) * r.den_s());
    assert((na * ((nb * nc) * bc.den_s())) * r.den_s() == (big * r.den_s()) * bc.den_s())
        by (nonlinear_arith)
        requires big == (na * nb) * nc;
    assert((r.num_s() * dend) * bc.den_s() == (big * r.den_s()) * bc.den_s());
    lemma_cancel_pos(r.num_s() * dend, big * r.den_s(), bc.den_s());

    assert(dend > 0) by (nonlinear_arith)
        requires da > 0, db > 0, dc > 0, dend == (da * db) * dc;
    lemma_common_value_qeq(l.num_s(), l.den_s(), r.num_s(), r.den_s(), big, dend);
    lemma_canonical_unique(l, r);
}

// ---------------------------------------------------------------------------
// Exact-path distributivity
// ---------------------------------------------------------------------------

/// `a * (b + c) == a*b + a*c` on the exact path.
pub proof fn theorem_distrib_exact(a: Q, b: Q, c: Q, bc: Q, ab: Q, ac: Q, l: Q, r: Q)
    requires
        a.inv(),
        b.inv(),
        c.inv(),
        bc.inv(),
        ab.inv(),
        ac.inv(),
        l.inv(),
        r.inv(),
        bc.is_frac(add_en(b, c), dd_ed(b, c)),
        l.is_frac(mul_en(a, bc), dd_ed(a, bc)),
        ab.is_frac(mul_en(a, b), dd_ed(a, b)),
        ac.is_frac(mul_en(a, c), dd_ed(a, c)),
        r.is_frac(add_en(ab, ac), dd_ed(ab, ac)),
    ensures
        l == r,
{
    let na = a.num_s();
    let da = a.den_s();
    let nb = b.num_s();
    let db = b.den_s();
    let nc = c.num_s();
    let dc = c.den_s();
    let e1 = na * (nb * dc + nc * db);
    let d1 = da * (db * dc);

    // ---- l == e1/d1: eliminate bc ----
    // Hl: l.num * (da * bc.den) == (na * bc.num) * l.den
    // Hbc: bc.num * (db * dc) == (nb*dc + nc*db) * bc.den
    let hll = l.num_s() * (da * bc.den_s());
    let hlr = (na * bc.num_s()) * l.den_s();
    assert(hll * (db * dc) == hlr * (db * dc));
    assert(hll * (db * dc) == (l.num_s() * d1) * bc.den_s()) by (nonlinear_arith)
        requires hll == l.num_s() * (da * bc.den_s()), d1 == da * (db * dc);
    assert(hlr * (db * dc) == (na * (bc.num_s() * (db * dc))) * l.den_s()) by (nonlinear_arith)
        requires hlr == (na * bc.num_s()) * l.den_s();
    assert((na * (bc.num_s() * (db * dc))) * l.den_s()
        == (na * ((nb * dc + nc * db) * bc.den_s())) * l.den_s());
    assert((na * ((nb * dc + nc * db) * bc.den_s())) * l.den_s() == (e1 * l.den_s()) * bc.den_s())
        by (nonlinear_arith)
        requires e1 == na * (nb * dc + nc * db);
    assert((l.num_s() * d1) * bc.den_s() == (e1 * l.den_s()) * bc.den_s());
    lemma_cancel_pos(l.num_s() * d1, e1 * l.den_s(), bc.den_s());

    // ---- r: eliminate ab ----
    // Hr: r.num * (ab.den * ac.den) == (ab.num * ac.den + ac.num * ab.den) * r.den
    // Hab: ab.num * (da * db) == (na * nb) * ab.den
    let hrl = r.num_s() * (ab.den_s() * ac.den_s());
    let hrr = (ab.num_s() * ac.den_s() + ac.num_s() * ab.den_s()) * r.den_s();
    assert(hrl * (da * db) == hrr * (da * db));
    assert(hrl * (da * db) == (r.num_s() * (ac.den_s() * (da * db))) * ab.den_s())
        by (nonlinear_arith)
        requires hrl == r.num_s() * (ab.den_s() * ac.den_s());
    assert(hrr * (da * db)
        == ((ab.num_s() * (da * db)) * ac.den_s()) * r.den_s()
            + ((ac.num_s() * (da * db)) * r.den_s()) * ab.den_s()) by {
        broadcast use vstd::arithmetic::mul::group_mul_properties;
    };
    assert(((ab.num_s() * (da * db)) * ac.den_s()) * r.den_s()
        == (((na * nb) * ab.den_s()) * ac.den_s()) * r.den_s());
    assert((((na * nb) * ab.den_s()) * ac.den_s()) * r.den_s()
        == (((na * nb) * ac.den_s()) * r.den_s()) * ab.den_s()) by (nonlinear_arith);
    assert((r.num_s() * (ac.den_s() * (da * db))) * ab.den_s()
        == (((na * nb) * ac.den_s()) * r.den_s() + ((ac.num_s() * (da * db)) * r.den_s()))
            * ab.den_s()) by (nonlinear_arith)
        requires
            (r.num_s() * (ac.den_s() * (da * db))) * ab.den_s()
                == (((na * nb) * ac.den_s()) * r.den_s()) * ab.den_s()
                    + ((ac.num_s() * (da * db)) * r.den_s()) * ab.den_s();
    lemma_cancel_pos(
        r.num_s() * (ac.den_s() * (da * db)),
        ((na * nb) * ac.den_s()) * r.den_s() + (ac.num_s() * (da * db)) * r.den_s(),
        ab.den_s(),
    );

    // ---- r: eliminate ac ----
    // Hac: ac.num * (da * dc) == (na * nc) * ac.den
    let h2l = r.num_s() * (ac.den_s() * (da * db));
    let h2r = ((na * nb) * ac.den_s()) * r.den_s() + (ac.num_s() * (da * db)) * r.den_s();
    assert(h2l * (da * dc) == h2r * (da * dc));
    assert(h2l * (da * dc) == (r.num_s() * ((da * db) * (da * dc))) * ac.den_s())
        by (nonlinear_arith)
        requires h2l == r.num_s() * (ac.den_s() * (da * db));
    assert(h2r * (da * dc)
        == (((na * nb) * (da * dc)) * r.den_s()) * ac.den_s()
            + (((ac.num_s() * (da * dc)) * (da * db)) * r.den_s())) by {
        broadcast use vstd::arithmetic::mul::group_mul_properties;
    };
    assert(((ac.num_s() * (da * dc)) * (da * db)) * r.den_s()
        == (((na * nc) * ac.den_s()) * (da * db)) * r.den_s());
    assert((((na * nc) * ac.den_s()) * (da * db)) * r.den_s()
        == (((na * nc) * (da * db)) * r.den_s()) * ac.den_s()) by (nonlinear_arith);
    assert((r.num_s() * ((da * db) * (da * dc))) * ac.den_s()
        == (((na * nb) * (da * dc)) * r.den_s() + ((na * nc) * (da * db)) * r.den_s())
            * ac.den_s()) by (nonlinear_arith)
        requires
            (r.num_s() * ((da * db) * (da * dc))) * ac.den_s()
                == (((na * nb) * (da * dc)) * r.den_s()) * ac.den_s()
                    + (((na * nc) * (da * db)) * r.den_s()) * ac.den_s();
    lemma_cancel_pos(
        r.num_s() * ((da * db) * (da * dc)),
        ((na * nb) * (da * dc)) * r.den_s() + ((na * nc) * (da * db)) * r.den_s(),
        ac.den_s(),
    );

    // ---- normalize r's value to (e1*da)/(d1*da) ----
    assert((na * nb) * (da * dc) + (na * nc) * (da * db) == e1 * da) by {
        broadcast use vstd::arithmetic::mul::group_mul_properties;
    };
    assert((da * db) * (da * dc) == d1 * da) by (nonlinear_arith)
        requires d1 == da * (db * dc);
    assert(((na * nb) * (da * dc)) * r.den_s() + ((na * nc) * (da * db)) * r.den_s()
        == (e1 * da) * r.den_s()) by (nonlinear_arith)
        requires (na * nb) * (da * dc) + (na * nc) * (da * db) == e1 * da;
    assert(r.num_s() * (d1 * da) == (e1 * da) * r.den_s());

    // ---- combine: l == e1/d1, r == (e1*da)/(d1*da) ----
    assert((l.num_s() * d1) * da == (e1 * l.den_s()) * da);
    assert((l.num_s() * d1) * da == l.num_s() * (d1 * da)) by (nonlinear_arith);
    assert((e1 * l.den_s()) * da == (e1 * da) * l.den_s()) by (nonlinear_arith);
    assert(l.num_s() * (d1 * da) == (e1 * da) * l.den_s());
    assert(d1 * da > 0) by (nonlinear_arith)
        requires da > 0, db > 0, dc > 0, d1 == da * (db * dc);
    lemma_common_value_qeq(l.num_s(), l.den_s(), r.num_s(), r.den_s(), e1 * da, d1 * da);
    lemma_canonical_unique(l, r);
}

// ---------------------------------------------------------------------------
// Involution laws
// ---------------------------------------------------------------------------

/// `-(-a) == a` (field-level, since neg is exact).
pub proof fn theorem_neg_involution(a: Q, n1: Q, n2: Q)
    requires
        a.inv(),
        n1.inv(),
        n2.inv(),
        n1.num_s() == -a.num_s() && n1.den_s() == a.den_s(),
        n2.num_s() == -n1.num_s() && n2.den_s() == n1.den_s(),
    ensures
        n2 == a,
{
    assert(n2.num_s() * a.den_s() == a.num_s() * n2.den_s());
    lemma_canonical_unique(n2, a);
}

/// `recip(recip(a)) == a` for nonzero `a` (via the recip field spec).
pub proof fn theorem_recip_involution(a: Q, r1: Q, r2: Q)
    requires
        a.inv(),
        r1.inv(),
        r2.inv(),
        a.num_s() != 0,
        r1.num_s() != 0,
        r1.num_s() * a.num_s() == r1.den_s() * a.den_s(),
        abs_i(r1.num_s()) == a.den_s(),
        r1.den_s() == abs_i(a.num_s()),
        r2.num_s() * r1.num_s() == r2.den_s() * r1.den_s(),
        abs_i(r2.num_s()) == r1.den_s(),
        r2.den_s() == abs_i(r1.num_s()),
    ensures
        r2 == a,
{
    // Signs: r1 has the sign of a; r2 has the sign of r1, hence of a.
    // Magnitudes: |r2.num| == r1.den == |a.num| and r2.den == |r1.num| == a.den.
    assert(r2.den_s() == a.den_s());
    if a.num_s() > 0 {
        assert(r1.num_s() > 0) by (nonlinear_arith)
            requires
                r1.num_s() * a.num_s() == r1.den_s() * a.den_s(),
                a.num_s() > 0,
                r1.den_s() > 0,
                a.den_s() > 0,
                r1.num_s() != 0;
        assert(r2.num_s() > 0) by (nonlinear_arith)
            requires
                r2.num_s() * r1.num_s() == r2.den_s() * r1.den_s(),
                r1.num_s() > 0,
                r2.den_s() > 0,
                r1.den_s() > 0;
        assert(r2.num_s() == a.num_s());
    } else {
        assert(r1.num_s() < 0) by (nonlinear_arith)
            requires
                r1.num_s() * a.num_s() == r1.den_s() * a.den_s(),
                a.num_s() < 0,
                r1.den_s() > 0,
                a.den_s() > 0;
        assert(r2.num_s() < 0) by (nonlinear_arith)
            requires
                r2.num_s() * r1.num_s() == r2.den_s() * r1.den_s(),
                r1.num_s() < 0,
                r2.den_s() > 0,
                r1.den_s() > 0;
        assert(r2.num_s() == a.num_s());
    }
    assert(r2.num_s() * a.den_s() == a.num_s() * r2.den_s());
    lemma_canonical_unique(r2, a);
}

} // verus!
