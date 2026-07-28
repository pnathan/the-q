//! Accumulated-error bounds for the n-ary fold helpers (obligation V8).
//!
//! The theorems: a chain of `Nearest`-rounded adds (resp. muls) over `k`
//! elements stays within `2k*w / 2^60` (i.e. `k*w*2^-59`) of the exact
//! fold, where `w` bounds the exact partial sums (resp. `w == 1` for
//! unit-interval products). Each step contributes at most one grid error
//! (R3) transported through the V7 Lipschitz lemmas; no error
//! amplification occurs because the transport is exact in the unperturbed
//! operand.

use vstd::prelude::*;
#[allow(unused_imports)]
use vstd::arithmetic::power2::*;

#[allow(unused_imports)]
use crate::arith::*;
#[allow(unused_imports)]
use crate::lipschitz::*;
#[allow(unused_imports)]
use crate::q::*;
#[allow(unused_imports)]
use crate::round::*;
#[allow(unused_imports)]
use crate::specs::*;

verus! {

/// Length cap for the fold theorems: 2^59 steps (far beyond any use).
pub open spec fn fold_len_cap() -> int {
    0x0800_0000_0000_0000
}

// ---------------------------------------------------------------------------
// Exact ghost folds
// ---------------------------------------------------------------------------

/// The exact rational value of the left add-fold, as an int fraction.
pub open spec fn exact_fold_add(xs: Seq<Q>) -> (int, int)
    decreases xs.len(),
{
    if xs.len() == 0 {
        (0int, 1int)
    } else {
        let p = exact_fold_add(xs.drop_last());
        let x = xs.last();
        (p.0 * x.den_s() + x.num_s() * p.1, p.1 * x.den_s())
    }
}

/// The exact rational value of the left mul-fold, as an int fraction.
pub open spec fn exact_fold_mul(xs: Seq<Q>) -> (int, int)
    decreases xs.len(),
{
    if xs.len() == 0 {
        (1int, 1int)
    } else {
        let p = exact_fold_mul(xs.drop_last());
        let x = xs.last();
        (p.0 * x.num_s(), p.1 * x.den_s())
    }
}

/// All elements satisfy the type invariant.
pub open spec fn all_inv(xs: Seq<Q>) -> bool {
    forall|i: int| 0 <= i < xs.len() ==> #[trigger] xs[i].inv()
}

/// All elements lie in [0, 1].
pub open spec fn all_unit(xs: Seq<Q>) -> bool {
    forall|i: int| 0 <= i < xs.len() ==> #[trigger] xs[i].in_unit_interval_s()
}

/// The exact partial sums of every prefix are bounded by `w` in magnitude.
pub open spec fn prefix_add_bounded(xs: Seq<Q>, w: int) -> bool {
    forall|i: int| 0 <= i <= xs.len()
        ==> #[trigger] frac_mag_le(exact_fold_add(xs.take(i)).0, exact_fold_add(xs.take(i)).1, w)
}

proof fn lemma_all_inv_prefix(xs: Seq<Q>)
    requires
        xs.len() > 0,
        all_inv(xs),
    ensures
        all_inv(xs.drop_last()),
        xs.last().inv(),
{
    assert forall|i: int| 0 <= i < xs.drop_last().len() implies #[trigger] xs.drop_last()[i].inv() by {
        assert(xs.drop_last()[i] == xs[i]);
        assert(xs[i].inv());
    }
    assert(xs[xs.len() - 1].inv());
}

proof fn lemma_fold_add_den_pos(xs: Seq<Q>)
    requires
        all_inv(xs),
    ensures
        exact_fold_add(xs).1 > 0,
    decreases xs.len(),
{
    if xs.len() == 0 {
    } else {
        lemma_all_inv_prefix(xs);
        lemma_fold_add_den_pos(xs.drop_last());
        assert(exact_fold_add(xs).1 > 0) by (nonlinear_arith)
            requires
                exact_fold_add(xs).1 == exact_fold_add(xs.drop_last()).1 * xs.last().den_s(),
                exact_fold_add(xs.drop_last()).1 > 0,
                xs.last().den_s() > 0;
    }
}

proof fn lemma_fold_mul_den_pos(xs: Seq<Q>)
    requires
        all_inv(xs),
    ensures
        exact_fold_mul(xs).1 > 0,
    decreases xs.len(),
{
    if xs.len() == 0 {
    } else {
        lemma_all_inv_prefix(xs);
        lemma_fold_mul_den_pos(xs.drop_last());
        assert(exact_fold_mul(xs).1 > 0) by (nonlinear_arith)
            requires
                exact_fold_mul(xs).1 == exact_fold_mul(xs.drop_last()).1 * xs.last().den_s(),
                exact_fold_mul(xs.drop_last()).1 > 0,
                xs.last().den_s() > 0;
    }
}

/// Unit-interval elements keep the exact mul-fold in [0, 1]:
/// `0 <= num <= den`.
proof fn lemma_fold_mul_unit(xs: Seq<Q>)
    requires
        all_inv(xs),
        all_unit(xs),
    ensures
        0 <= exact_fold_mul(xs).0,
        exact_fold_mul(xs).0 <= exact_fold_mul(xs).1,
    decreases xs.len(),
{
    if xs.len() == 0 {
    } else {
        lemma_all_inv_prefix(xs);
        assert forall|i: int| 0 <= i < xs.drop_last().len()
            implies #[trigger] xs.drop_last()[i].in_unit_interval_s() by {
            assert(xs.drop_last()[i] == xs[i]);
            assert(xs[i].in_unit_interval_s());
        }
        lemma_fold_mul_unit(xs.drop_last());
        let p = exact_fold_mul(xs.drop_last());
        let x = xs.last();
        assert(xs[xs.len() - 1].in_unit_interval_s());
        assert(0 <= p.0 * x.num_s() && p.0 * x.num_s() <= p.1 * x.den_s()) by (nonlinear_arith)
            requires
                0 <= p.0,
                p.0 <= p.1,
                0 <= x.num_s(),
                x.num_s() <= x.den_s();
    }
}

// ---------------------------------------------------------------------------
// Chain predicates: what the exec folds actually produce
// ---------------------------------------------------------------------------

/// Step `i` of the add chain: `accs[i+1]` is the Nearest-rounded sum of
/// `accs[i]` and `xs[i]`.
pub open spec fn add_step_ok(xs: Seq<Q>, accs: Seq<Q>, i: int) -> bool
    recommends
        0 <= i < xs.len(),
        accs.len() == xs.len() + 1,
{
    &&& accs[i].inv()
    &&& accs[i + 1].inv()
    &&& round_char(accs[i + 1], add_en(accs[i], xs[i]), dd_ed(accs[i], xs[i]), Dir::Nearest)
}

/// The whole add chain, starting from zero.
pub open spec fn add_chain_ok(xs: Seq<Q>, accs: Seq<Q>) -> bool {
    &&& accs.len() == xs.len() + 1
    &&& accs[0].inv()
    &&& accs[0].num_s() == 0
    &&& accs[0].den_s() == 1
    &&& forall|i: int| 0 <= i < xs.len() ==> #[trigger] add_step_ok(xs, accs, i)
}

/// Step `i` of the mul chain.
pub open spec fn mul_step_ok(xs: Seq<Q>, accs: Seq<Q>, i: int) -> bool
    recommends
        0 <= i < xs.len(),
        accs.len() == xs.len() + 1,
{
    &&& accs[i].inv()
    &&& accs[i + 1].inv()
    &&& round_char(accs[i + 1], mul_en(accs[i], xs[i]), dd_ed(accs[i], xs[i]), Dir::Nearest)
}

/// The whole mul chain, starting from one.
pub open spec fn mul_chain_ok(xs: Seq<Q>, accs: Seq<Q>) -> bool {
    &&& accs.len() == xs.len() + 1
    &&& accs[0].inv()
    &&& accs[0].num_s() == 1
    &&& accs[0].den_s() == 1
    &&& forall|i: int| 0 <= i < xs.len() ==> #[trigger] mul_step_ok(xs, accs, i)
}

// ---------------------------------------------------------------------------
// Helper lemmas
// ---------------------------------------------------------------------------

/// Magnitude transport: close to a `m`-bounded value with slack `en/ed <= m`
/// means bounded by `2m`.
proof fn lemma_mag_transport(an: int, ad: int, bn: int, bd: int, m: int, en: int, ed: int)
    requires
        ad > 0,
        bd > 0,
        ed > 0,
        m >= 0,
        en <= m * ed,
        frac_close(an, ad, bn, bd, en, ed),
        frac_mag_le(bn, bd, m),
    ensures
        frac_mag_le(an, ad, 2 * m),
{
    // Upper: an*(bd*ed) <= (2m*ad)*(bd*ed), then cancel bd*ed.
    assert(an * (bd * ed) <= ((2 * m) * ad) * (bd * ed)) by (nonlinear_arith)
        requires
            (an * bd - bn * ad) * ed <= en * (ad * bd),
            bn <= m * bd,
            en <= m * ed,
            ad > 0,
            bd > 0,
            ed > 0,
            m >= 0;
    assert(an <= (2 * m) * ad) by (nonlinear_arith)
        requires an * (bd * ed) <= ((2 * m) * ad) * (bd * ed), bd > 0, ed > 0;
    // Lower side, mirrored.
    assert((-((2 * m) * ad)) * (bd * ed) <= an * (bd * ed)) by (nonlinear_arith)
        requires
            -(en * (ad * bd)) <= (an * bd - bn * ad) * ed,
            -(m * bd) <= bn,
            en <= m * ed,
            ad > 0,
            bd > 0,
            ed > 0,
            m >= 0;
    assert(-((2 * m) * ad) <= an) by (nonlinear_arith)
        requires (-((2 * m) * ad)) * (bd * ed) <= an * (bd * ed), bd > 0, ed > 0;
}

/// Convert the R3 clause of `rounds_to` into a `frac_close` with cap `c`:
/// requires `|en| <= c*ed` (value magnitude within the cap) and `c >= 1`.
proof fn lemma_r3_to_close(q: Q, en: int, ed: int, c: int, dir: Dir)
    requires
        ed > 0,
        c >= 1,
        q.inv(),
        rounds_to(q, en, ed, dir),
        -(c * ed) <= en,
        en <= c * ed,
        2 * c <= max_mag(),
    ensures
        frac_close(q.num_s(), q.den_s(), en, ed, c, pow2(60) as int),
{
    let diff = q.num_s() * ed - en * q.den_s();
    let p60 = pow2(60) as int;
    lemma_pow2_pos(60);
    // The R2/R3 guard |en| <= MAX * ed holds since c <= MAX.
    assert(abs_i(en) <= max_mag() * ed) by (nonlinear_arith)
        requires
            -(c * ed) <= en,
            en <= c * ed,
            2 * c <= max_mag(),
            c >= 1,
            ed > 0;
    // Case split from R3.
    if abs_i(en) <= ed {
        assert(abs_i(diff) * p60 <= q.den_s() * ed);
        assert(abs_i(diff) * p60 <= c * (q.den_s() * ed)) by (nonlinear_arith)
            requires
                abs_i(diff) * p60 <= q.den_s() * ed,
                c >= 1,
                q.den_s() > 0,
                ed > 0;
    } else {
        assert(abs_i(diff) * p60 <= q.den_s() * abs_i(en));
        assert(abs_i(diff) * p60 <= c * (q.den_s() * ed)) by (nonlinear_arith)
            requires
                abs_i(diff) * p60 <= q.den_s() * abs_i(en),
                -(c * ed) <= en,
                en <= c * ed,
                (en >= 0 ==> abs_i(en) == en) && (en < 0 ==> abs_i(en) == -en),
                q.den_s() > 0,
                ed > 0;
    }
    // Two-sided form from the abs bound.
    assert(diff * p60 <= abs_i(diff) * p60 && -(abs_i(diff) * p60) <= diff * p60)
        by (nonlinear_arith)
        requires
            (diff >= 0 ==> abs_i(diff) == diff) && (diff < 0 ==> abs_i(diff) == -diff),
            p60 > 0;
    assert(-(c * (q.den_s() * ed)) <= diff * p60 && diff * p60 <= c * (q.den_s() * ed));
}

// ---------------------------------------------------------------------------
// V8 main theorems
// ---------------------------------------------------------------------------

/// Accumulated error of a rounded add-fold: within `2*k*w / 2^60`
/// (`== k*w*2^-59`) of the exact sum, provided every exact partial sum is
/// bounded by `w`.
pub proof fn theorem_fold_add_error(xs: Seq<Q>, accs: Seq<Q>, w: int)
    requires
        all_inv(xs),
        add_chain_ok(xs, accs),
        prefix_add_bounded(xs, w),
        w >= 1,
        4 * w <= max_mag(),
        xs.len() <= fold_len_cap(),
    ensures
        frac_close(
            accs[xs.len() as int].num_s(),
            accs[xs.len() as int].den_s(),
            exact_fold_add(xs).0,
            exact_fold_add(xs).1,
            2 * (xs.len() as int) * w,
            pow2(60) as int,
        ),
    decreases xs.len(),
{
    let n = xs.len() as int;
    let p60 = pow2(60) as int;
    lemma_pow2_pos(60);
    lemma2_to64_rest();
    if n == 0 {
        assert(frac_close(accs[0].num_s(), accs[0].den_s(), 0, 1, 0, p60)) by (nonlinear_arith)
            requires
                accs[0].num_s() == 0,
                accs[0].den_s() == 1,
                p60 > 0;
    } else {
        let xs0 = xs.drop_last();
        let accs0 = accs.drop_last();
        lemma_all_inv_prefix(xs);
        // Sub-chain hypotheses.
        assert(accs0.len() == xs0.len() + 1);
        assert(accs0[0] == accs[0]);
        assert forall|i: int| 0 <= i < xs0.len() implies #[trigger] add_step_ok(xs0, accs0, i) by {
            assert(add_step_ok(xs, accs, i));
            assert(accs0[i] == accs[i] && accs0[i + 1] == accs[i + 1] && xs0[i] == xs[i]);
        }
        assert forall|i: int| 0 <= i <= xs0.len()
            implies #[trigger] frac_mag_le(
                exact_fold_add(xs0.take(i)).0, exact_fold_add(xs0.take(i)).1, w) by {
            assert(xs0.take(i) =~= xs.take(i));
            assert(frac_mag_le(exact_fold_add(xs.take(i)).0, exact_fold_add(xs.take(i)).1, w));
        }
        theorem_fold_add_error(xs0, accs0, w);
        // Names for the step.
        let acc = accs[n - 1];
        let next = accs[n];
        let x = xs[n - 1];
        let s = exact_fold_add(xs0);
        let t = exact_fold_add(xs);
        assert(accs0[xs0.len() as int] == acc);
        assert(xs.last() == x);
        assert(t.0 == s.0 * x.den_s() + x.num_s() * s.1 && t.1 == s.1 * x.den_s());
        lemma_fold_add_den_pos(xs0);
        lemma_fold_add_den_pos(xs);
        assert(add_step_ok(xs, accs, n - 1));
        assert(acc.inv() && next.inv() && x.inv());
        let e0 = 2 * (n - 1) * w;
        // Transport the inherited error through the exact addition step.
        lemma_close_refl(x.num_s(), x.den_s(), 0, p60);
        lemma_lip_add(
            acc.num_s(), acc.den_s(), s.0, s.1,
            x.num_s(), x.den_s(), x.num_s(), x.den_s(),
            e0, 0, p60);
        let un = acc.num_s() * x.den_s() + x.num_s() * acc.den_s();
        let ud = acc.den_s() * x.den_s();
        assert(ud > 0) by (nonlinear_arith)
            requires ud == acc.den_s() * x.den_s(), acc.den_s() > 0, x.den_s() > 0;
        assert(frac_close(
            un, ud,
            s.0 * x.den_s() + x.num_s() * s.1, s.1 * x.den_s(),
            e0 + 0, p60));
        assert(e0 + 0 == e0);
        assert(t.1 > 0);
        lemma_close_weaken(un, ud, t.0, t.1, e0 + 0, e0, p60);
        assert(frac_close(un, ud, t.0, t.1, e0, p60));
        // |t| <= w  (prefix bound at the full length).
        assert(xs.take(n) =~= xs);
        assert(frac_mag_le(t.0, t.1, w));
        // |u| <= 2w.
        assert(e0 <= w * p60) by (nonlinear_arith)
            requires
                e0 == 2 * (n - 1) * w,
                n <= fold_len_cap(),
                fold_len_cap() == 0x0800_0000_0000_0000,
                p60 == pow2(60),
                pow2(60) == 0x1000_0000_0000_0000,
                w >= 1,
                n >= 1;
        lemma_mag_transport(un, ud, t.0, t.1, w, e0, p60);
        // The rounding step: R3 at cap 2w.
        assert(add_en(acc, x) == un && dd_ed(acc, x) == ud);
        lemma_round_char_correct(next, un, ud, Dir::Nearest);
        assert(-((2 * w) * ud) <= un && un <= (2 * w) * ud);
        assert(2 * (2 * w) <= max_mag()) by (nonlinear_arith)
            requires 4 * w <= max_mag();
        lemma_r3_to_close(next, un, ud, 2 * w, Dir::Nearest);
        // Triangle: next ~ u ~ t.
        lemma_frac_triangle(
            next.num_s(), next.den_s(), un, ud, t.0, t.1, 2 * w, e0, p60);
        assert(2 * w + e0 == 2 * n * w) by (nonlinear_arith)
            requires e0 == 2 * (n - 1) * w;
    }
}

/// Accumulated error of a rounded mul-fold over unit-interval elements:
/// within `2*k / 2^60` (`== k*2^-59`) of the exact product.
pub proof fn theorem_fold_mul_error(xs: Seq<Q>, accs: Seq<Q>)
    requires
        all_inv(xs),
        all_unit(xs),
        mul_chain_ok(xs, accs),
        xs.len() <= fold_len_cap(),
    ensures
        frac_close(
            accs[xs.len() as int].num_s(),
            accs[xs.len() as int].den_s(),
            exact_fold_mul(xs).0,
            exact_fold_mul(xs).1,
            2 * (xs.len() as int),
            pow2(60) as int,
        ),
    decreases xs.len(),
{
    let n = xs.len() as int;
    let p60 = pow2(60) as int;
    lemma_pow2_pos(60);
    lemma2_to64_rest();
    if n == 0 {
        assert(frac_close(accs[0].num_s(), accs[0].den_s(), 1, 1, 0, p60)) by (nonlinear_arith)
            requires
                accs[0].num_s() == 1,
                accs[0].den_s() == 1,
                p60 > 0;
    } else {
        let xs0 = xs.drop_last();
        let accs0 = accs.drop_last();
        lemma_all_inv_prefix(xs);
        assert forall|i: int| 0 <= i < xs0.len()
            implies #[trigger] xs0[i].in_unit_interval_s() by {
            assert(xs0[i] == xs[i]);
            assert(xs[i].in_unit_interval_s());
        }
        assert forall|i: int| 0 <= i < xs0.len() implies #[trigger] mul_step_ok(xs0, accs0, i) by {
            assert(mul_step_ok(xs, accs, i));
            assert(accs0[i] == accs[i] && accs0[i + 1] == accs[i + 1] && xs0[i] == xs[i]);
        }
        theorem_fold_mul_error(xs0, accs0);
        let acc = accs[n - 1];
        let next = accs[n];
        let x = xs[n - 1];
        let s = exact_fold_mul(xs0);
        let t = exact_fold_mul(xs);
        assert(accs0[xs0.len() as int] == acc);
        assert(xs.last() == x);
        assert(t.0 == s.0 * x.num_s() && t.1 == s.1 * x.den_s());
        lemma_fold_mul_den_pos(xs0);
        lemma_fold_mul_den_pos(xs);
        lemma_fold_mul_unit(xs0);
        lemma_fold_mul_unit(xs);
        assert(mul_step_ok(xs, accs, n - 1));
        assert(acc.inv() && next.inv() && x.inv());
        assert(xs[n - 1].in_unit_interval_s());
        let e0 = 2 * (n - 1);
        // |s| <= 1, |acc| <= 2 (transport), |x| <= 1.
        assert(frac_mag_le(s.0, s.1, 1)) by (nonlinear_arith)
            requires 0 <= s.0, s.0 <= s.1, s.1 > 0;
        assert(e0 <= 1 * p60) by (nonlinear_arith)
            requires
                e0 == 2 * (n - 1),
                n <= fold_len_cap(),
                fold_len_cap() == 0x0800_0000_0000_0000,
                p60 == pow2(60),
                pow2(60) == 0x1000_0000_0000_0000,
                n >= 1;
        lemma_mag_transport(acc.num_s(), acc.den_s(), s.0, s.1, 1, e0, p60);
        // Transport the inherited error through the exact multiplication:
        // e1 side is acc~s with |x| <= 1 as the fixed factor (mb == 1),
        // and e2 == 0 with |acc| <= 2 (ma == 2).
        lemma_close_refl(x.num_s(), x.den_s(), 0, p60);
        assert(frac_mag_le(x.num_s(), x.den_s(), 1)) by (nonlinear_arith)
            requires 0 <= x.num_s(), x.num_s() <= x.den_s(), x.den_s() > 0;
        lemma_lip_mul(
            acc.num_s(), acc.den_s(), s.0, s.1,
            x.num_s(), x.den_s(), x.num_s(), x.den_s(),
            2, 1, e0, 0, p60);
        let un = acc.num_s() * x.num_s();
        let ud = acc.den_s() * x.den_s();
        assert(ud > 0) by (nonlinear_arith)
            requires ud == acc.den_s() * x.den_s(), acc.den_s() > 0, x.den_s() > 0;
        assert(frac_close(un, ud, s.0 * x.num_s(), s.1 * x.den_s(), 1 * e0 + 2 * 0, p60));
        assert(1 * e0 + 2 * 0 == e0) by (nonlinear_arith);
        assert(t.1 > 0);
        lemma_close_weaken(un, ud, t.0, t.1, 1 * e0 + 2 * 0, e0, p60);
        assert(frac_close(un, ud, t.0, t.1, e0, p60));
        // |u| <= 2: |acc| <= 2 and |x| <= 1.
        assert(-(2 * ud) <= un && un <= 2 * ud) by (nonlinear_arith)
            requires
                -(2 * acc.den_s()) <= acc.num_s() && acc.num_s() <= 2 * acc.den_s(),
                0 <= x.num_s() && x.num_s() <= x.den_s(),
                acc.den_s() > 0,
                x.den_s() > 0,
                un == acc.num_s() * x.num_s(),
                ud == acc.den_s() * x.den_s();
        // The rounding step at cap 2.
        assert(mul_en(acc, x) == un && dd_ed(acc, x) == ud);
        lemma_round_char_correct(next, un, ud, Dir::Nearest);
        assert(2 * 2 <= max_mag());
        lemma_r3_to_close(next, un, ud, 2, Dir::Nearest);
        // Triangle.
        lemma_frac_triangle(
            next.num_s(), next.den_s(), un, ud, t.0, t.1, 2, e0, p60);
        assert(2 + e0 == 2 * n) by (nonlinear_arith)
            requires e0 == 2 * (n - 1);
    }
}

} // verus!
