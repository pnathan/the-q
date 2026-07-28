//! Interval arithmetic `QI = [lo, hi]` on the directed rounding modes
//! (milestone M6, stretch).
//!
//! Each op rounds the lower endpoint `Down` and the upper endpoint `Up`,
//! so intervals always *enclose* the exact real result - proven by the
//! `lemma_qi_*_encloses` theorems against arbitrary exact rationals
//! (which need not be representable). Multiplication is provided for
//! nonnegative intervals (the engine's opinion space).

use vstd::prelude::*;
#[allow(unused_imports)]
use vstd::arithmetic::mul::*;

#[allow(unused_imports)]
use crate::arith::*;
#[allow(unused_imports)]
use crate::q::*;
#[allow(unused_imports)]
use crate::round::*;
#[allow(unused_imports)]
use crate::specs::*;

verus! {

/// A closed interval of rationals.
#[derive(Clone, Copy, PartialEq, Eq, Structural)]
pub struct QI {
    pub lo: Q,
    pub hi: Q,
}

impl QI {
    /// Invariant: both endpoints canonical and ordered.
    pub open spec fn inv(self) -> bool {
        &&& self.lo.inv()
        &&& self.hi.inv()
        &&& q_le(self.lo, self.hi)
    }

    /// The exact rational `n/d` (`d > 0`) lies in this interval.
    pub open spec fn contains_frac(self, n: int, d: int) -> bool
        recommends
            d > 0,
    {
        &&& self.lo.num_s() * d <= n * self.lo.den_s()
        &&& n * self.hi.den_s() <= self.hi.num_s() * d
    }

    /// Degenerate (point) interval.
    pub fn point(x: Q) -> (r: QI)
        requires
            x.inv(),
        ensures
            r.inv(),
            r.lo == x,
            r.hi == x,
    {
        QI { lo: x, hi: x }
    }

    /// Construct from ordered endpoints.
    pub fn new_qi(lo: Q, hi: Q) -> (r: Option<QI>)
        requires
            lo.inv(),
            hi.inv(),
        ensures
            r is Some <==> q_le(lo, hi),
            r is Some ==> r.unwrap().inv() && r.unwrap().lo == lo && r.unwrap().hi == hi,
    {
        if lo.le(hi) {
            Some(QI { lo, hi })
        } else {
            None
        }
    }

    /// Interval addition: lower endpoint rounds Down, upper rounds Up.
    /// The endpoint sums must be within the representable magnitude range
    /// (trivial for the engine's [0, 1] opinion space) so that directed
    /// rounding cannot saturate.
    pub fn add(self, rhs: QI) -> (r: QI)
        requires
            self.inv(),
            rhs.inv(),
            abs_i(add_en(self.lo, rhs.lo)) <= max_mag() * dd_ed(self.lo, rhs.lo),
            abs_i(add_en(self.hi, rhs.hi)) <= max_mag() * dd_ed(self.hi, rhs.hi),
        ensures
            r.inv(),
            round_char(r.lo, add_en(self.lo, rhs.lo), dd_ed(self.lo, rhs.lo), Dir::Down),
            round_char(r.hi, add_en(self.hi, rhs.hi), dd_ed(self.hi, rhs.hi), Dir::Up),
    {
        let lo = self.lo.add_dir(rhs.lo, Dir::Down);
        let hi = self.hi.add_dir(rhs.hi, Dir::Up);
        proof {
            lemma_dir_endpoints_ordered(
                self.lo, rhs.lo, self.hi, rhs.hi, lo, hi);
        }
        QI { lo, hi }
    }

    /// Interval subtraction: `[a.lo - b.hi, a.hi - b.lo]`, outward-rounded.
    /// Same non-saturation preconditions as `add`.
    pub fn sub(self, rhs: QI) -> (r: QI)
        requires
            self.inv(),
            rhs.inv(),
            abs_i(sub_en(self.lo, rhs.hi)) <= max_mag() * dd_ed(self.lo, rhs.hi),
            abs_i(sub_en(self.hi, rhs.lo)) <= max_mag() * dd_ed(self.hi, rhs.lo),
        ensures
            r.inv(),
            round_char(r.lo, sub_en(self.lo, rhs.hi), dd_ed(self.lo, rhs.hi), Dir::Down),
            round_char(r.hi, sub_en(self.hi, rhs.lo), dd_ed(self.hi, rhs.lo), Dir::Up),
    {
        let n = rhs.neg();
        proof {
            assert(add_en(self.lo, n.lo) == sub_en(self.lo, rhs.hi)) by {
                lemma_mul_unary_negation(n.lo.num_s(), self.lo.den_s());
            };
            assert(dd_ed(self.lo, n.lo) == dd_ed(self.lo, rhs.hi));
            assert(add_en(self.hi, n.hi) == sub_en(self.hi, rhs.lo)) by {
                lemma_mul_unary_negation(n.hi.num_s(), self.hi.den_s());
            };
            assert(dd_ed(self.hi, n.hi) == dd_ed(self.hi, rhs.lo));
        }
        let r = self.add(n);
        r
    }

    /// Interval negation: exact.
    pub fn neg(self) -> (r: QI)
        requires
            self.inv(),
        ensures
            r.inv(),
            r.lo.num_s() == -self.hi.num_s() && r.lo.den_s() == self.hi.den_s(),
            r.hi.num_s() == -self.lo.num_s() && r.hi.den_s() == self.lo.den_s(),
    {
        let lo = self.hi.neg();
        let hi = self.lo.neg();
        proof {
            assert(q_le(lo, hi)) by (nonlinear_arith)
                requires
                    lo.num_s() == -self.hi.num_s(),
                    lo.den_s() == self.hi.den_s(),
                    hi.num_s() == -self.lo.num_s(),
                    hi.den_s() == self.lo.den_s(),
                    self.lo.num_s() * self.hi.den_s() <= self.hi.num_s() * self.lo.den_s();
        }
        QI { lo, hi }
    }

    /// Is every value in the interval nonnegative?
    pub open spec fn nonneg(self) -> bool {
        self.lo.num_s() >= 0
    }

    /// Interval multiplication for nonnegative intervals. The upper
    /// product must be within the representable magnitude range (trivial
    /// for [0, 1] opinion values).
    pub fn mul_nonneg(self, rhs: QI) -> (r: QI)
        requires
            self.inv(),
            rhs.inv(),
            self.nonneg(),
            rhs.nonneg(),
            mul_en(self.hi, rhs.hi) <= max_mag() * dd_ed(self.hi, rhs.hi),
        ensures
            r.inv(),
            round_char(r.lo, mul_en(self.lo, rhs.lo), dd_ed(self.lo, rhs.lo), Dir::Down),
            round_char(r.hi, mul_en(self.hi, rhs.hi), dd_ed(self.hi, rhs.hi), Dir::Up),
    {
        let lo = self.lo.mul_dir(rhs.lo, Dir::Down);
        let hi = self.hi.mul_dir(rhs.hi, Dir::Up);
        proof {
            // lo <= lo1*lo2 <= hi1*hi2 <= hi (monotone mul on nonnegatives).
            let en1 = mul_en(self.lo, rhs.lo);
            let ed1 = dd_ed(self.lo, rhs.lo);
            let en2 = mul_en(self.hi, rhs.hi);
            let ed2 = dd_ed(self.hi, rhs.hi);
            lemma_ed_pos(self.lo, rhs.lo);
            lemma_ed_pos(self.hi, rhs.hi);
            // hi1*hi2 >= lo1*lo2 (nonneg monotone), cross-multiplied.
            assert(self.hi.num_s() >= 0) by (nonlinear_arith)
                requires
                    self.lo.num_s() >= 0,
                    self.lo.num_s() * self.hi.den_s() <= self.hi.num_s() * self.lo.den_s(),
                    self.lo.den_s() > 0,
                    self.hi.den_s() > 0;
            assert(rhs.hi.num_s() >= 0) by (nonlinear_arith)
                requires
                    rhs.lo.num_s() >= 0,
                    rhs.lo.num_s() * rhs.hi.den_s() <= rhs.hi.num_s() * rhs.lo.den_s(),
                    rhs.lo.den_s() > 0,
                    rhs.hi.den_s() > 0;
            lemma_frac_mul_mono(
                self.lo.num_s(), self.lo.den_s(), self.hi.num_s(), self.hi.den_s(),
                rhs.lo.num_s(), rhs.lo.den_s(), rhs.hi.num_s(), rhs.hi.den_s());
            // The lower product inherits the range bound from the upper one.
            lemma_lower_product_in_range(self, rhs, en1, ed1, en2, ed2);
            lemma_round_char_correct(lo, en1, ed1, Dir::Down);
            lemma_round_char_correct(hi, en2, ed2, Dir::Up);
            // Chain through the two rounded endpoints.
            lemma_le_through_rounding(lo, hi, en1, ed1, en2, ed2);
        }
        QI { lo, hi }
    }
}

// ---------------------------------------------------------------------------
// Support lemmas
// ---------------------------------------------------------------------------

proof fn lemma_ed_pos(a: Q, b: Q)
    requires
        a.inv(),
        b.inv(),
    ensures
        dd_ed(a, b) > 0,
{
    assert(a.den_s() * b.den_s() > 0) by (nonlinear_arith)
        requires a.den_s() > 0, b.den_s() > 0;
}

/// For nonnegative intervals with the upper product in range, the lower
/// product is in range too (`0 <= en1/ed1 <= en2/ed2 <= MAX`).
proof fn lemma_lower_product_in_range(a: QI, b: QI, en1: int, ed1: int, en2: int, ed2: int)
    requires
        a.inv(),
        b.inv(),
        a.nonneg(),
        b.nonneg(),
        en1 == mul_en(a.lo, b.lo),
        ed1 == dd_ed(a.lo, b.lo),
        en2 == mul_en(a.hi, b.hi),
        ed2 == dd_ed(a.hi, b.hi),
        ed1 > 0,
        ed2 > 0,
        en1 * ed2 <= en2 * ed1,
        en2 <= max_mag() * ed2,
    ensures
        abs_i(en1) <= max_mag() * ed1,
        abs_i(en2) <= max_mag() * ed2,
{
    assert(en1 >= 0) by (nonlinear_arith)
        requires
            en1 == a.lo.num_s() * b.lo.num_s(),
            a.lo.num_s() >= 0,
            b.lo.num_s() >= 0;
    assert(en2 >= 0) by (nonlinear_arith)
        requires
            en1 * ed2 <= en2 * ed1,
            en1 >= 0,
            ed1 > 0,
            ed2 > 0;
    // en1 <= MAX*ed1: from en1*ed2 <= en2*ed1 <= (MAX*ed2)*ed1.
    lemma_mul_inequality(en2, max_mag() * ed2, ed1);
    assert((max_mag() * ed2) * ed1 == (max_mag() * ed1) * ed2) by (nonlinear_arith);
    assert(en1 <= max_mag() * ed1) by (nonlinear_arith)
        requires en1 * ed2 <= (max_mag() * ed1) * ed2, ed2 > 0;
}

/// From `lo <=(as frac) en1/ed1`, `en1/ed1 <= en2/ed2`, `en2/ed2 <= hi`
/// conclude `q_le(lo, hi)`.
proof fn lemma_le_through_rounding(lo: Q, hi: Q, en1: int, ed1: int, en2: int, ed2: int)
    requires
        lo.inv(),
        hi.inv(),
        ed1 > 0,
        ed2 > 0,
        lo.num_s() * ed1 - en1 * lo.den_s() <= 0,
        hi.num_s() * ed2 - en2 * hi.den_s() >= 0,
        en1 * ed2 <= en2 * ed1,
    ensures
        q_le(lo, hi),
{
    // lo <= en1/ed1 <= en2/ed2 <= hi, all cross-multiplied.
    lemma_frac_le_trans(
        lo.num_s(), lo.den_s(), en1, ed1, en2, ed2);
    lemma_frac_le_trans(
        lo.num_s(), lo.den_s(), en2, ed2, hi.num_s(), hi.den_s());
}

/// Transitivity of `<=` on fractions with positive denominators.
proof fn lemma_frac_le_trans(an: int, ad: int, bn: int, bd: int, cn: int, cd: int)
    requires
        ad > 0,
        bd > 0,
        cd > 0,
        an * bd <= bn * ad,
        bn * cd <= cn * bd,
    ensures
        an * cd <= cn * ad,
{
    assert((an * cd) * bd == (an * bd) * cd) by (nonlinear_arith);
    lemma_mul_inequality(an * bd, bn * ad, cd);
    assert((bn * ad) * cd == (bn * cd) * ad) by (nonlinear_arith);
    lemma_mul_inequality(bn * cd, cn * bd, ad);
    assert((cn * bd) * ad == (cn * ad) * bd) by (nonlinear_arith);
    assert((an * cd) * bd <= (cn * ad) * bd);
    assert(an * cd <= cn * ad) by (nonlinear_arith)
        requires (an * cd) * bd <= (cn * ad) * bd, bd > 0;
}

/// Ordered endpoints after directed rounding of ordered exact sums.
proof fn lemma_dir_endpoints_ordered(al: Q, bl: Q, ah: Q, bh: Q, lo: Q, hi: Q)
    requires
        al.inv(),
        bl.inv(),
        ah.inv(),
        bh.inv(),
        lo.inv(),
        hi.inv(),
        q_le(al, ah),
        q_le(bl, bh),
        abs_i(add_en(al, bl)) <= max_mag() * dd_ed(al, bl),
        abs_i(add_en(ah, bh)) <= max_mag() * dd_ed(ah, bh),
        round_char(lo, add_en(al, bl), dd_ed(al, bl), Dir::Down),
        round_char(hi, add_en(ah, bh), dd_ed(ah, bh), Dir::Up),
    ensures
        q_le(lo, hi),
{
    let en1 = add_en(al, bl);
    let ed1 = dd_ed(al, bl);
    let en2 = add_en(ah, bh);
    let ed2 = dd_ed(ah, bh);
    lemma_ed_pos(al, bl);
    lemma_ed_pos(ah, bh);
    lemma_round_char_correct(lo, en1, ed1, Dir::Down);
    lemma_round_char_correct(hi, en2, ed2, Dir::Up);
    lemma_frac_add_mono(
        al.num_s(), al.den_s(), ah.num_s(), ah.den_s(),
        bl.num_s(), bl.den_s(), bh.num_s(), bh.den_s());
    lemma_le_through_rounding(lo, hi, en1, ed1, en2, ed2);
}

/// Monotonicity of exact fraction addition:
/// `l <= x` and `m <= y` give `l + m <= x + y` (cross-multiplied).
proof fn lemma_frac_add_mono(
    ln: int, ld: int, xn: int, xd: int, mn: int, md: int, yn: int, yd: int)
    requires
        ld > 0,
        xd > 0,
        md > 0,
        yd > 0,
        ln * xd <= xn * ld,
        mn * yd <= yn * md,
    ensures
        (ln * md + mn * ld) * (xd * yd) <= (xn * yd + yn * xd) * (ld * md),
{
    lemma_mul_is_distributive_add_other_way(xd * yd, ln * md, mn * ld);
    lemma_mul_is_distributive_add_other_way(ld * md, xn * yd, yn * xd);
    // term 1: (ln*md)*(xd*yd) == (ln*xd)*(md*yd) <= (xn*ld)*(md*yd) == (xn*yd)*(ld*md)
    assert((ln * md) * (xd * yd) == (ln * xd) * (md * yd)) by (nonlinear_arith);
    lemma_mul_inequality(ln * xd, xn * ld, md * yd);
    assert(md * yd >= 0) by (nonlinear_arith) requires md > 0, yd > 0;
    assert((xn * ld) * (md * yd) == (xn * yd) * (ld * md)) by (nonlinear_arith);
    // term 2: (mn*ld)*(xd*yd) == (mn*yd)*(ld*xd) <= (yn*md)*(ld*xd) == (yn*xd)*(ld*md)
    assert((mn * ld) * (xd * yd) == (mn * yd) * (ld * xd)) by (nonlinear_arith);
    lemma_mul_inequality(mn * yd, yn * md, ld * xd);
    assert(ld * xd >= 0) by (nonlinear_arith) requires ld > 0, xd > 0;
    assert((yn * md) * (ld * xd) == (yn * xd) * (ld * md)) by (nonlinear_arith);
}

/// Monotonicity of exact fraction multiplication on nonnegatives:
/// `0 <= l <= x`, `0 <= m <= y` give `l*m <= x*y` (cross-multiplied).
proof fn lemma_frac_mul_mono(
    ln: int, ld: int, xn: int, xd: int, mn: int, md: int, yn: int, yd: int)
    requires
        ld > 0,
        xd > 0,
        md > 0,
        yd > 0,
        ln >= 0,
        mn >= 0,
        ln * xd <= xn * ld,
        mn * yd <= yn * md,
    ensures
        (ln * mn) * (xd * yd) <= (xn * yn) * (ld * md),
{
    // x and y are nonnegative too.
    assert(xn >= 0) by (nonlinear_arith)
        requires ln >= 0, ln * xd <= xn * ld, ld > 0, xd > 0;
    assert(yn >= 0) by (nonlinear_arith)
        requires mn >= 0, mn * yd <= yn * md, md > 0, yd > 0;
    // (ln*mn)*(xd*yd) == (ln*xd)*(mn*yd) <= (xn*ld)*(mn*yd)
    //   <= (xn*ld)*(yn*md) == (xn*yn)*(ld*md)
    assert((ln * mn) * (xd * yd) == (ln * xd) * (mn * yd)) by (nonlinear_arith);
    assert(mn * yd >= 0) by (nonlinear_arith) requires mn >= 0, yd > 0;
    lemma_mul_inequality(ln * xd, xn * ld, mn * yd);
    assert(xn * ld >= 0) by (nonlinear_arith) requires xn >= 0, ld > 0;
    assert((xn * ld) * (mn * yd) <= (xn * ld) * (yn * md)) by (nonlinear_arith)
        requires mn * yd <= yn * md, xn * ld >= 0;
    assert((xn * ld) * (yn * md) == (xn * yn) * (ld * md)) by (nonlinear_arith);
}

// ---------------------------------------------------------------------------
// Enclosure theorems: intervals contain the exact results
// ---------------------------------------------------------------------------

/// If `x in a` and `y in b` (as exact rationals), then the exact sum
/// `x + y` lies in `a.add(b)`.
pub proof fn lemma_qi_add_encloses(
    a: QI, b: QI, r: QI, xn: int, xd: int, yn: int, yd: int)
    requires
        a.inv(),
        b.inv(),
        r.inv(),
        xd > 0,
        yd > 0,
        a.contains_frac(xn, xd),
        b.contains_frac(yn, yd),
        abs_i(add_en(a.lo, b.lo)) <= max_mag() * dd_ed(a.lo, b.lo),
        abs_i(add_en(a.hi, b.hi)) <= max_mag() * dd_ed(a.hi, b.hi),
        round_char(r.lo, add_en(a.lo, b.lo), dd_ed(a.lo, b.lo), Dir::Down),
        round_char(r.hi, add_en(a.hi, b.hi), dd_ed(a.hi, b.hi), Dir::Up),
    ensures
        r.contains_frac(xn * yd + yn * xd, xd * yd),
{
    let en1 = add_en(a.lo, b.lo);
    let ed1 = dd_ed(a.lo, b.lo);
    let en2 = add_en(a.hi, b.hi);
    let ed2 = dd_ed(a.hi, b.hi);
    lemma_ed_pos(a.lo, b.lo);
    lemma_ed_pos(a.hi, b.hi);
    assert(xd * yd > 0) by (nonlinear_arith) requires xd > 0, yd > 0;
    lemma_round_char_correct(r.lo, en1, ed1, Dir::Down);
    lemma_round_char_correct(r.hi, en2, ed2, Dir::Up);
    // lo <= lo1+lo2 <= x+y: monotone add, then transitivity.
    lemma_frac_add_mono(
        a.lo.num_s(), a.lo.den_s(), xn, xd,
        b.lo.num_s(), b.lo.den_s(), yn, yd);
    lemma_frac_le_trans(
        r.lo.num_s(), r.lo.den_s(), en1, ed1, xn * yd + yn * xd, xd * yd);
    // x+y <= hi1+hi2 <= hi.
    lemma_frac_add_mono(
        xn, xd, a.hi.num_s(), a.hi.den_s(),
        yn, yd, b.hi.num_s(), b.hi.den_s());
    lemma_frac_le_trans(
        xn * yd + yn * xd, xd * yd, en2, ed2, r.hi.num_s(), r.hi.den_s());
}

/// If `x in a` and `y in b` with everything nonnegative, the exact product
/// `x * y` lies in `a.mul_nonneg(b)`.
pub proof fn lemma_qi_mul_encloses(
    a: QI, b: QI, r: QI, xn: int, xd: int, yn: int, yd: int)
    requires
        a.inv(),
        b.inv(),
        r.inv(),
        xd > 0,
        yd > 0,
        a.nonneg(),
        b.nonneg(),
        a.contains_frac(xn, xd),
        b.contains_frac(yn, yd),
        mul_en(a.hi, b.hi) <= max_mag() * dd_ed(a.hi, b.hi),
        round_char(r.lo, mul_en(a.lo, b.lo), dd_ed(a.lo, b.lo), Dir::Down),
        round_char(r.hi, mul_en(a.hi, b.hi), dd_ed(a.hi, b.hi), Dir::Up),
    ensures
        r.contains_frac(xn * yn, xd * yd),
{
    let en1 = mul_en(a.lo, b.lo);
    let ed1 = dd_ed(a.lo, b.lo);
    let en2 = mul_en(a.hi, b.hi);
    let ed2 = dd_ed(a.hi, b.hi);
    lemma_ed_pos(a.lo, b.lo);
    lemma_ed_pos(a.hi, b.hi);
    assert(xd * yd > 0) by (nonlinear_arith) requires xd > 0, yd > 0;
    assert(a.hi.num_s() >= 0) by (nonlinear_arith)
        requires
            a.lo.num_s() >= 0,
            a.lo.num_s() * a.hi.den_s() <= a.hi.num_s() * a.lo.den_s(),
            a.lo.den_s() > 0,
            a.hi.den_s() > 0;
    assert(b.hi.num_s() >= 0) by (nonlinear_arith)
        requires
            b.lo.num_s() >= 0,
            b.lo.num_s() * b.hi.den_s() <= b.hi.num_s() * b.lo.den_s(),
            b.lo.den_s() > 0,
            b.hi.den_s() > 0;
    lemma_frac_mul_mono(
        a.lo.num_s(), a.lo.den_s(), a.hi.num_s(), a.hi.den_s(),
        b.lo.num_s(), b.lo.den_s(), b.hi.num_s(), b.hi.den_s());
    lemma_lower_product_in_range(a, b, en1, ed1, en2, ed2);
    lemma_round_char_correct(r.lo, en1, ed1, Dir::Down);
    lemma_round_char_correct(r.hi, en2, ed2, Dir::Up);
    // lo <= lo1*lo2 <= x*y.
    lemma_frac_mul_mono(
        a.lo.num_s(), a.lo.den_s(), xn, xd,
        b.lo.num_s(), b.lo.den_s(), yn, yd);
    lemma_frac_le_trans(
        r.lo.num_s(), r.lo.den_s(), en1, ed1, xn * yn, xd * yd);
    // x*y <= hi1*hi2 <= hi (x, y nonnegative from containment).
    assert(xn >= 0) by (nonlinear_arith)
        requires
            a.lo.num_s() >= 0,
            a.lo.num_s() * xd <= xn * a.lo.den_s(),
            a.lo.den_s() > 0,
            xd > 0;
    assert(yn >= 0) by (nonlinear_arith)
        requires
            b.lo.num_s() >= 0,
            b.lo.num_s() * yd <= yn * b.lo.den_s(),
            b.lo.den_s() > 0,
            yd > 0;
    lemma_frac_mul_mono(
        xn, xd, a.hi.num_s(), a.hi.den_s(),
        yn, yd, b.hi.num_s(), b.hi.den_s());
    lemma_frac_le_trans(
        xn * yn, xd * yd, en2, ed2, r.hi.num_s(), r.hi.den_s());
}

} // verus!
