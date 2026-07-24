//! Binary arithmetic on `Q` (obligations V2 + V3): exact i128
//! intermediates, then the verified reduce-or-round pipeline.
//!
//! Every op ensures both `round_char` (the unique result characterization,
//! for determinism/algebra theorems) and `rounds_to` (the R1-R3 contract)
//! against its exact ghost formula, stated division-free.

use vstd::prelude::*;

#[allow(unused_imports)]
use crate::q::*;
#[allow(unused_imports)]
use crate::round::*;
#[allow(unused_imports)]
use crate::specs::*;

verus! {

// ---------------------------------------------------------------------------
// Exact ghost formulas for each op (division-free cross-multiplied model)
// ---------------------------------------------------------------------------

/// Exact numerator of `a + b` over the common denominator `dd_ed(a, b)`.
pub open spec fn add_en(a: Q, b: Q) -> int {
    a.num_s() * b.den_s() + b.num_s() * a.den_s()
}

/// Exact numerator of `a - b` over the common denominator `dd_ed(a, b)`.
pub open spec fn sub_en(a: Q, b: Q) -> int {
    a.num_s() * b.den_s() - b.num_s() * a.den_s()
}

/// Exact numerator of `a * b`.
pub open spec fn mul_en(a: Q, b: Q) -> int {
    a.num_s() * b.num_s()
}

/// Exact (positive) denominator shared by add/sub/mul: `a.den * b.den`.
pub open spec fn dd_ed(a: Q, b: Q) -> int {
    a.den_s() * b.den_s()
}

/// Exact numerator of `a / b`, sign-normalized so the denominator is positive.
pub open spec fn div_en(a: Q, b: Q) -> int {
    if b.num_s() < 0 {
        -(a.num_s() * b.den_s())
    } else {
        a.num_s() * b.den_s()
    }
}

/// Exact positive denominator of `a / b`: `a.den * |b.num|`.
pub open spec fn div_ed(a: Q, b: Q) -> int {
    a.den_s() * abs_i(b.num_s())
}

// ---------------------------------------------------------------------------
// Shared plumbing: signed i128 fraction -> round_frac
// ---------------------------------------------------------------------------

/// `1 <= x * y <= (2^62 - 1)^2`, as one trigger-friendly predicate.
pub open spec fn ed_pos_bound(x: int, y: int) -> bool {
    1 <= x * y <= 0x0FFF_FFFF_FFFF_FFFF_8000_0000_0000_0001
}

/// Feed a signed, bounded i128 fraction through the rounding pipeline.
fn round_i128(en: i128, ed: i128, dir: Dir) -> (q: Q)
    requires
        ed > 0,
        -0x2000_0000_0000_0000_0000_0000_0000_0000 < en as int,  // |en| < 2^125
        (en as int) < 0x2000_0000_0000_0000_0000_0000_0000_0000,
        (ed as int) < 0x2000_0000_0000_0000_0000_0000_0000_0000,
    ensures
        q.inv(),
        round_char(q, en as int, ed as int, dir),
        rounds_to(q, en as int, ed as int, dir),
{
    let neg = en < 0;
    let un: u128 = if neg { (-en) as u128 } else { en as u128 };
    let q = round_frac(neg, un, ed as u128, dir);
    proof {
        assert(signed(neg, un as int) == en as int);
        lemma_round_char_correct(q, en as int, ed as int, dir);
    }
    q
}

impl Q {
    // -----------------------------------------------------------------------
    // Addition / subtraction
    // -----------------------------------------------------------------------

    /// `self + rhs`, rounding per `dir` when the exact result exceeds the
    /// budget (exact otherwise, per R1).
    pub fn add_dir(self, rhs: Q, dir: Dir) -> (r: Q)
        requires
            self.inv(),
            rhs.inv(),
        ensures
            r.inv(),
            round_char(r, add_en(self, rhs), dd_ed(self, rhs), dir),
            rounds_to(r, add_en(self, rhs), dd_ed(self, rhs), dir),
    {
        let (en, ed) = self.add_frac(rhs);
        round_i128(en, ed, dir)
    }

    /// Exact `a + b` fraction in i128 (small helper, small SMT query).
    fn add_frac(self, rhs: Q) -> (r: (i128, i128))
        requires
            self.inv(),
            rhs.inv(),
        ensures
            r.0 as int == add_en(self, rhs),
            r.1 as int == dd_ed(self, rhs),
            r.1 > 0,
            -0x2000_0000_0000_0000_0000_0000_0000_0000 < r.0 as int,
            (r.0 as int) < 0x2000_0000_0000_0000_0000_0000_0000_0000,
            (r.1 as int) < 0x2000_0000_0000_0000_0000_0000_0000_0000,
    {
        proof {
            lemma_q_fields(self);
            lemma_q_fields(rhs);
            lemma_cross_bound(self.num_s(), rhs.den_s());
            lemma_cross_bound(rhs.num_s(), self.den_s());
            lemma_cross_bound(self.den_s(), rhs.den_s());
            assert(ed_pos_bound(self.den_s(), rhs.den_s())) by (nonlinear_arith)
                requires
                    1 <= self.den_s() <= max_mag(),
                    1 <= rhs.den_s() <= max_mag();
        }
        let p1: i128 = (self.num as i128) * (rhs.den as i128);
        let p2: i128 = (rhs.num as i128) * (self.den as i128);
        let en: i128 = p1 + p2;
        let ed: i128 = (self.den as i128) * (rhs.den as i128);
        (en, ed)
    }

    /// `self - rhs` (see `add_dir`).
    pub fn sub_dir(self, rhs: Q, dir: Dir) -> (r: Q)
        requires
            self.inv(),
            rhs.inv(),
        ensures
            r.inv(),
            round_char(r, sub_en(self, rhs), dd_ed(self, rhs), dir),
            rounds_to(r, sub_en(self, rhs), dd_ed(self, rhs), dir),
    {
        let n = rhs.neg();
        let r = self.add_dir(n, dir);
        proof {
            assert(self.num_s() * n.den_s() + n.num_s() * self.den_s()
                == self.num_s() * rhs.den_s() - rhs.num_s() * self.den_s())
                by (nonlinear_arith)
                requires
                    n.num_s() == -rhs.num_s(),
                    n.den_s() == rhs.den_s();
            assert(add_en(self, n) == sub_en(self, rhs));
            assert(dd_ed(self, n) == dd_ed(self, rhs));
        }
        r
    }

    // -----------------------------------------------------------------------
    // Multiplication
    // -----------------------------------------------------------------------

    /// `self * rhs` (see `add_dir`).
    pub fn mul_dir(self, rhs: Q, dir: Dir) -> (r: Q)
        requires
            self.inv(),
            rhs.inv(),
        ensures
            r.inv(),
            round_char(r, mul_en(self, rhs), dd_ed(self, rhs), dir),
            rounds_to(r, mul_en(self, rhs), dd_ed(self, rhs), dir),
    {
        let (en, ed) = self.mul_frac(rhs);
        round_i128(en, ed, dir)
    }

    /// Exact `a * b` fraction in i128 (small helper, small SMT query).
    fn mul_frac(self, rhs: Q) -> (r: (i128, i128))
        requires
            self.inv(),
            rhs.inv(),
        ensures
            r.0 as int == mul_en(self, rhs),
            r.1 as int == dd_ed(self, rhs),
            r.1 > 0,
            -0x2000_0000_0000_0000_0000_0000_0000_0000 < r.0 as int,
            (r.0 as int) < 0x2000_0000_0000_0000_0000_0000_0000_0000,
            (r.1 as int) < 0x2000_0000_0000_0000_0000_0000_0000_0000,
    {
        proof {
            lemma_q_fields(self);
            lemma_q_fields(rhs);
            lemma_cross_bound_signed(self.num_s(), rhs.num_s());
            lemma_cross_bound(self.den_s(), rhs.den_s());
            assert(ed_pos_bound(self.den_s(), rhs.den_s())) by (nonlinear_arith)
                requires
                    1 <= self.den_s() <= max_mag(),
                    1 <= rhs.den_s() <= max_mag();
        }
        let en: i128 = (self.num as i128) * (rhs.num as i128);
        let ed: i128 = (self.den as i128) * (rhs.den as i128);
        (en, ed)
    }

    // -----------------------------------------------------------------------
    // Division
    // -----------------------------------------------------------------------

    /// `self / rhs`. Division by zero is a *precondition* (`rhs` nonzero),
    /// discharged statically by the caller - there is no runtime panic path.
    pub fn div_dir(self, rhs: Q, dir: Dir) -> (r: Q)
        requires
            self.inv(),
            rhs.inv(),
            rhs.num_s() != 0,
        ensures
            r.inv(),
            round_char(r, div_en(self, rhs), div_ed(self, rhs), dir),
            rounds_to(r, div_en(self, rhs), div_ed(self, rhs), dir),
    {
        let (en, ed) = self.div_frac(rhs);
        round_i128(en, ed, dir)
    }

    /// Sign-normalized exact fraction of `self / rhs` in i128 (helper kept
    /// separate so its query stays small).
    fn div_frac(self, rhs: Q) -> (r: (i128, i128))
        requires
            self.inv(),
            rhs.inv(),
            rhs.num_s() != 0,
        ensures
            r.0 as int == div_en(self, rhs),
            r.1 as int == div_ed(self, rhs),
            r.1 > 0,
            -0x2000_0000_0000_0000_0000_0000_0000_0000 < r.0 as int,
            (r.0 as int) < 0x2000_0000_0000_0000_0000_0000_0000_0000,
            (r.1 as int) < 0x2000_0000_0000_0000_0000_0000_0000_0000,
    {
        proof {
            lemma_q_fields(self);
            lemma_q_fields(rhs);
            lemma_cross_bound(self.num_s(), rhs.den_s());
        }
        let en_raw: i128 = (self.num as i128) * (rhs.den as i128);
        let en: i128 = if rhs.num < 0 { -en_raw } else { en_raw };
        let ud: i128 = if rhs.num < 0 { -(rhs.num as i128) } else { rhs.num as i128 };
        proof {
            assert(abs_i(rhs.num_s()) == ud as int);
            assert(1 <= ud as int && ud as int <= max_mag());
            assert(en as int == div_en(self, rhs));
            assert(ed_pos_bound(self.den_s(), ud as int)) by (nonlinear_arith)
                requires 1 <= self.den_s() <= max_mag(), 1 <= ud as int && ud as int <= max_mag();
        }
        let ed: i128 = (self.den as i128) * ud;
        proof {
            assert(ed as int == div_ed(self, rhs));
        }
        (en, ed)
    }

    // -----------------------------------------------------------------------
    // Default (Nearest) wrappers
    // -----------------------------------------------------------------------

    /// `self + rhs` with `Dir::Nearest`.
    pub fn add(self, rhs: Q) -> (r: Q)
        requires
            self.inv(),
            rhs.inv(),
        ensures
            r.inv(),
            round_char(r, add_en(self, rhs), dd_ed(self, rhs), Dir::Nearest),
            rounds_to(r, add_en(self, rhs), dd_ed(self, rhs), Dir::Nearest),
    {
        self.add_dir(rhs, Dir::Nearest)
    }

    /// `self - rhs` with `Dir::Nearest`.
    pub fn sub(self, rhs: Q) -> (r: Q)
        requires
            self.inv(),
            rhs.inv(),
        ensures
            r.inv(),
            round_char(r, sub_en(self, rhs), dd_ed(self, rhs), Dir::Nearest),
            rounds_to(r, sub_en(self, rhs), dd_ed(self, rhs), Dir::Nearest),
    {
        self.sub_dir(rhs, Dir::Nearest)
    }

    /// `self * rhs` with `Dir::Nearest`.
    pub fn mul(self, rhs: Q) -> (r: Q)
        requires
            self.inv(),
            rhs.inv(),
        ensures
            r.inv(),
            round_char(r, mul_en(self, rhs), dd_ed(self, rhs), Dir::Nearest),
            rounds_to(r, mul_en(self, rhs), dd_ed(self, rhs), Dir::Nearest),
    {
        self.mul_dir(rhs, Dir::Nearest)
    }

    /// `self / rhs` with `Dir::Nearest`; `rhs` nonzero is a precondition.
    pub fn div(self, rhs: Q) -> (r: Q)
        requires
            self.inv(),
            rhs.inv(),
            rhs.num_s() != 0,
        ensures
            r.inv(),
            round_char(r, div_en(self, rhs), div_ed(self, rhs), Dir::Nearest),
            rounds_to(r, div_en(self, rhs), div_ed(self, rhs), Dir::Nearest),
    {
        self.div_dir(rhs, Dir::Nearest)
    }
}

} // verus!
