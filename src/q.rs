//! The `Q` type: canonical bounded rationals (invariants I1 + I2), the
//! canonical constructor, exact unary operations, and exact comparisons.

use vstd::prelude::*;

#[allow(unused_imports)]
use crate::gcd::*;
#[allow(unused_imports)]
use crate::specs::*;

verus! {

/// A rational number `num / den` in canonical form:
///
/// - I1 (canonical): `den > 0`, `gcd(|num|, den) == 1`
/// - I2 (bounded): `|num| <= 2^62 - 1`, `den <= 2^62 - 1`
///
/// Canonical form makes structural equality coincide with mathematical
/// equality, so the derived `PartialEq`/`Eq` are semantically correct
/// (see `lemma_canonical_unique`).
#[derive(Clone, Copy, PartialEq, Eq, Structural)]
pub struct Q {
    num: i64,
    den: i64,
}

// ---------------------------------------------------------------------------
// Ghost model
// ---------------------------------------------------------------------------

/// Mathematical equality of the represented rationals (division-free).
pub open spec fn q_eq(a: Q, b: Q) -> bool {
    a.num_s() * b.den_s() == b.num_s() * a.den_s()
}

/// Mathematical `<=` on the represented rationals (denominators positive).
pub open spec fn q_le(a: Q, b: Q) -> bool {
    a.num_s() * b.den_s() <= b.num_s() * a.den_s()
}

/// Mathematical `<` on the represented rationals.
pub open spec fn q_lt(a: Q, b: Q) -> bool {
    a.num_s() * b.den_s() < b.num_s() * a.den_s()
}

impl Q {
    /// Ghost numerator.
    pub closed spec fn num_s(self) -> int {
        self.num as int
    }

    /// Ghost denominator.
    pub closed spec fn den_s(self) -> int {
        self.den as int
    }

    /// The type invariant: I1 (canonical) and I2 (bounded).
    pub open spec fn inv(self) -> bool {
        &&& 0 < self.den_s() <= max_mag()
        &&& -max_mag() <= self.num_s() <= max_mag()
        &&& gcd(abs_i(self.num_s()) as nat, self.den_s() as nat) == 1
    }

    /// `self == n / d` as a division-free cross-multiplication.
    pub open spec fn is_frac(self, n: int, d: int) -> bool {
        self.num_s() * d == n * self.den_s()
    }

    /// `0 <= self <= 1`, phrased on the canonical fields.
    pub open spec fn in_unit_interval_s(self) -> bool {
        0 <= self.num_s() && self.num_s() <= self.den_s()
    }
}

// ---------------------------------------------------------------------------
// Canonical construction
// ---------------------------------------------------------------------------

/// Does `num / den` (den != 0) fit the I2 budget once fully reduced?
pub open spec fn new_fits(num: int, den: int) -> bool
    recommends
        den != 0,
{
    let g = gcd(abs_i(num) as nat, abs_i(den) as nat);
    abs_i(num) as nat / g <= max_mag() && abs_i(den) as nat / g <= max_mag()
}

/// |x| as u128, total on all of i64 (including `i64::MIN`).
pub(crate) fn abs_i64_u128(x: i64) -> (r: u128)
    ensures
        r as int == abs_i(x as int),
{
    if x < 0 {
        (-(x as i128)) as u128
    } else {
        x as u128
    }
}

/// Reduce `sign * (un / ud)` to canonical form; `None` iff the reduced
/// magnitudes exceed the I2 budget. This is the single canonicalization
/// path shared by all constructors.
pub(crate) fn make_canonical(neg: bool, un: u128, ud: u128) -> (r: Option<Q>)
    requires
        ud > 0,
    ensures
        ({
            let g = gcd(un as nat, ud as nat);
            let rn = un as nat / g;
            let rd = ud as nat / g;
            &&& (r is Some <==> (rn <= max_mag() && rd <= max_mag()))
            &&& un as nat == g * rn
            &&& ud as nat == g * rd
            &&& g > 0
            &&& (r is Some ==> {
                let q = r.unwrap();
                &&& q.inv()
                &&& q.num_s() == if neg { -(rn as int) } else { rn as int }
                &&& q.den_s() == rd as int
            })
        }),
{
    let g = gcd_u128(un, ud);
    proof {
        lemma_gcd_pos(un as nat, ud as nat);
        lemma_gcd_divides(un as nat, ud as nat);
        lemma_div_exact(g as nat, un as nat);
        lemma_div_exact(g as nat, ud as nat);
    }
    let rn = un / g;
    let rd = ud / g;
    proof {
        assert(rd >= 1) by (nonlinear_arith)
            requires ud as nat == g as nat * (rd as nat), ud > 0, g > 0;
        lemma_gcd_div_gcd_is_one(un as nat, ud as nat);
    }
    if rn <= MAX_MAG as u128 && rd <= MAX_MAG as u128 {
        let num: i64 = if neg { -(rn as i64) } else { rn as i64 };
        let q = Q { num, den: rd as i64 };
        proof {
            assert(abs_i(q.num_s()) == rn as int);
            assert(gcd(abs_i(q.num_s()) as nat, q.den_s() as nat) == 1);
        }
        Some(q)
    } else {
        None
    }
}

impl Q {
    /// The rational 0 (canonically `0/1`).
    pub fn zero() -> (r: Q)
        ensures
            r.inv(),
            r.num_s() == 0,
            r.den_s() == 1,
    {
        proof { lemma_gcd_x_one(0); }
        Q { num: 0, den: 1 }
    }

    /// The rational 1 (canonically `1/1`).
    pub fn one() -> (r: Q)
        ensures
            r.inv(),
            r.num_s() == 1,
            r.den_s() == 1,
    {
        proof { lemma_gcd_x_one(1); }
        Q { num: 1, den: 1 }
    }

    /// Exact integer embedding; `None` iff `|i| > 2^62 - 1`.
    pub fn from_int(i: i64) -> (r: Option<Q>)
        ensures
            r is Some <==> -max_mag() <= i as int <= max_mag(),
            r is Some ==> {
                let q = r.unwrap();
                &&& q.inv()
                &&& q.num_s() == i as int
                &&& q.den_s() == 1
            },
    {
        if -MAX_MAG <= i && i <= MAX_MAG {
            proof { lemma_gcd_x_one(abs_i(i as int) as nat); }
            Some(Q { num: i, den: 1 })
        } else {
            None
        }
    }

    /// Canonicalizing constructor. `None` iff `den == 0` or the fully
    /// reduced form exceeds the I2 budget (only possible when a magnitude
    /// exceeds `2^62 - 1` and the gcd does not shrink it back into range).
    /// Never rounds: the returned value is exactly `num / den`.
    pub fn new(num: i64, den: i64) -> (r: Option<Q>)
        ensures
            den == 0 ==> r is None,
            den != 0 ==> (r is Some <==> new_fits(num as int, den as int)),
            r is Some ==> {
                let q = r.unwrap();
                &&& q.inv()
                &&& q.num_s() * (den as int) == (num as int) * q.den_s()
            },
    {
        if den == 0 {
            return None;
        }
        let neg = (num < 0) != (den < 0);
        let un = abs_i64_u128(num);
        let ud = abs_i64_u128(den);
        let r = make_canonical(neg, un, ud);
        proof {
            let g = gcd(un as nat, ud as nat);
            let rn = (un as nat / g) as int;
            let rd = (ud as nat / g) as int;
            if r is Some {
                let q = r.unwrap();
                // Magnitude identity: rn * ud == un * rd, since un == g*rn, ud == g*rd.
                assert(rn * (ud as int) == (un as int) * rd) by (nonlinear_arith)
                    requires
                        un as int == g as int * rn,
                        ud as int == g as int * rd;
                // Push signs through the cross-multiplication, case by case.
                if num >= 0 && den > 0 {
                    assert(q.num_s() * (den as int) == (num as int) * q.den_s())
                        by (nonlinear_arith)
                        requires
                            rn * (ud as int) == (un as int) * rd,
                            q.num_s() == rn,
                            q.den_s() == rd,
                            num as int == un as int,
                            den as int == ud as int;
                } else if num < 0 && den > 0 {
                    assert(q.num_s() * (den as int) == (num as int) * q.den_s())
                        by (nonlinear_arith)
                        requires
                            rn * (ud as int) == (un as int) * rd,
                            q.num_s() == -rn,
                            q.den_s() == rd,
                            num as int == -(un as int),
                            den as int == ud as int;
                } else if num >= 0 && den < 0 {
                    assert(q.num_s() * (den as int) == (num as int) * q.den_s())
                        by (nonlinear_arith)
                        requires
                            rn * (ud as int) == (un as int) * rd,
                            q.num_s() == -rn,
                            q.den_s() == rd,
                            num as int == un as int,
                            den as int == -(ud as int);
                } else {
                    assert(q.num_s() * (den as int) == (num as int) * q.den_s())
                        by (nonlinear_arith)
                        requires
                            rn * (ud as int) == (un as int) * rd,
                            q.num_s() == rn,
                            q.den_s() == rd,
                            num as int == -(un as int),
                            den as int == -(ud as int);
                }
            }
        }
        r
    }
}

// ---------------------------------------------------------------------------
// Uniqueness of canonical form
// ---------------------------------------------------------------------------

/// Two canonical representations of the same rational are structurally
/// identical. This is what makes the derived `Eq`/`Hash` semantically
/// correct and `cmp` antisymmetric.
pub proof fn lemma_canonical_unique(a: Q, b: Q)
    requires
        a.inv(),
        b.inv(),
        q_eq(a, b),
    ensures
        a == b,
{
    let n1 = a.num_s();
    let d1 = a.den_s();
    let n2 = b.num_s();
    let d2 = b.den_s();
    if n1 == 0 {
        assert(n2 * d1 == 0) by (nonlinear_arith)
            requires n1 * d2 == n2 * d1, n1 == 0;
        assert(n2 == 0) by (nonlinear_arith)
            requires n2 * d1 == 0, d1 > 0;
        // gcd(0, d) == d, so canonicality forces den == 1 on both sides.
        vstd::arithmetic::div_mod::lemma_small_mod(0, d1 as nat);
        vstd::arithmetic::div_mod::lemma_small_mod(0, d2 as nat);
        assert(gcd(0, d1 as nat) == gcd(d1 as nat, 0));
        assert(gcd(0, d2 as nat) == gcd(d2 as nat, 0));
        assert(d1 == 1 && d2 == 1);
    } else {
        // Signs agree.
        assert(n2 != 0) by (nonlinear_arith)
            requires n1 * d2 == n2 * d1, d1 > 0, d2 > 0, n1 != 0;
        assert((n1 > 0) == (n2 > 0)) by (nonlinear_arith)
            requires n1 * d2 == n2 * d1, d1 > 0, d2 > 0, n1 != 0, n2 != 0;
        // Magnitudes cross-multiply equally.
        let m1 = abs_i(n1) as nat;
        let m2 = abs_i(n2) as nat;
        assert(m1 * d2 as nat == m2 * d1 as nat) by (nonlinear_arith)
            requires
                n1 * d2 == n2 * d1,
                d1 > 0,
                d2 > 0,
                (n1 > 0) == (n2 > 0),
                m1 == abs_i(n1),
                m2 == abs_i(n2);
        // Coprimality gives mutual divisibility of the denominators.
        lemma_coprime_divides(m1, d1 as nat, d2 as nat, m2);
        lemma_coprime_divides(m2, d2 as nat, d1 as nat, m1);
        lemma_divides_le(d1 as nat, d2 as nat);
        lemma_divides_le(d2 as nat, d1 as nat);
        assert(d1 == d2);
        assert(n1 == n2) by (nonlinear_arith)
            requires n1 * d2 == n2 * d1, d1 == d2, d1 > 0;
    }
}

// ---------------------------------------------------------------------------
// Exact comparisons (i128 cross-multiplication; no overflow under I2)
// ---------------------------------------------------------------------------

/// Bound for cross-multiplication products: |x*y| <= max_mag()^2 < 2^124.
proof fn lemma_cross_bound(x: int, y: int)
    requires
        -max_mag() <= x <= max_mag(),
        0 <= y <= max_mag(),
    ensures
        -max_mag() * max_mag() <= x * y <= max_mag() * max_mag(),
{
    assert(-max_mag() * max_mag() <= x * y <= max_mag() * max_mag()) by (nonlinear_arith)
        requires -max_mag() <= x <= max_mag(), 0 <= y <= max_mag();
}

impl Q {
    /// Exact `<=` (no epsilon, total).
    pub fn le(self, rhs: Q) -> (r: bool)
        requires
            self.inv(),
            rhs.inv(),
        ensures
            r == q_le(self, rhs),
    {
        proof {
            lemma_cross_bound(self.num_s(), rhs.den_s());
            lemma_cross_bound(rhs.num_s(), self.den_s());
        }
        (self.num as i128) * (rhs.den as i128) <= (rhs.num as i128) * (self.den as i128)
    }

    /// Exact `<`.
    pub fn lt(self, rhs: Q) -> (r: bool)
        requires
            self.inv(),
            rhs.inv(),
        ensures
            r == q_lt(self, rhs),
    {
        proof {
            lemma_cross_bound(self.num_s(), rhs.den_s());
            lemma_cross_bound(rhs.num_s(), self.den_s());
        }
        (self.num as i128) * (rhs.den as i128) < (rhs.num as i128) * (self.den as i128)
    }

    /// Exact three-way comparison, agreeing with the ghost order.
    pub fn cmp_q(self, rhs: Q) -> (r: core::cmp::Ordering)
        requires
            self.inv(),
            rhs.inv(),
        ensures
            r is Less <==> q_lt(self, rhs),
            r is Equal <==> q_eq(self, rhs),
            r is Greater <==> q_lt(rhs, self),
            r is Equal <==> self == rhs,
    {
        proof {
            lemma_cross_bound(self.num_s(), rhs.den_s());
            lemma_cross_bound(rhs.num_s(), self.den_s());
            if q_eq(self, rhs) {
                lemma_canonical_unique(self, rhs);
            }
        }
        let lhs = (self.num as i128) * (rhs.den as i128);
        let r = (rhs.num as i128) * (self.den as i128);
        if lhs < r {
            core::cmp::Ordering::Less
        } else if lhs == r {
            core::cmp::Ordering::Equal
        } else {
            core::cmp::Ordering::Greater
        }
    }

    /// Exact equality test (equivalent to `==` by canonical uniqueness).
    pub fn eq_q(self, rhs: Q) -> (r: bool)
        requires
            self.inv(),
            rhs.inv(),
        ensures
            r == q_eq(self, rhs),
            r == (self == rhs),
    {
        proof {
            if q_eq(self, rhs) {
                lemma_canonical_unique(self, rhs);
            }
        }
        matches!(self.cmp_q(rhs), core::cmp::Ordering::Equal)
    }
}

// ---------------------------------------------------------------------------
// Exact unary operations and predicates
// ---------------------------------------------------------------------------

impl Q {
    /// Negation; always exact (I2 is symmetric in sign).
    pub fn neg(self) -> (r: Q)
        requires
            self.inv(),
        ensures
            r.inv(),
            r.num_s() == -self.num_s(),
            r.den_s() == self.den_s(),
    {
        Q { num: -self.num, den: self.den }
    }

    /// Absolute value; always exact.
    pub fn abs(self) -> (r: Q)
        requires
            self.inv(),
        ensures
            r.inv(),
            r.num_s() == abs_i(self.num_s()),
            r.den_s() == self.den_s(),
    {
        if self.num < 0 {
            Q { num: -self.num, den: self.den }
        } else {
            self
        }
    }

    /// Reciprocal; always exact (swaps numerator and denominator).
    /// Division by zero is a precondition, discharged statically.
    pub fn recip(self) -> (r: Q)
        requires
            self.inv(),
            self.num_s() != 0,
        ensures
            r.inv(),
            r.num_s() * self.num_s() == r.den_s() * self.den_s(),
            abs_i(r.num_s()) == self.den_s(),
            r.den_s() == abs_i(self.num_s()),
    {
        proof {
            lemma_gcd_symm(abs_i(self.num_s()) as nat, self.den_s() as nat);
        }
        if self.num < 0 {
            let r = Q { num: -self.den, den: -self.num };
            proof {
                assert(r.num_s() * self.num_s() == r.den_s() * self.den_s())
                    by (nonlinear_arith)
                    requires
                        r.num_s() == -self.den_s(),
                        r.den_s() == -self.num_s();
            }
            r
        } else {
            Q { num: self.den, den: self.num }
        }
    }

    /// Is this exactly zero?
    pub fn is_zero(self) -> (r: bool)
        requires
            self.inv(),
        ensures
            r == (self.num_s() == 0),
    {
        self.num == 0
    }

    /// Is this exactly one?
    pub fn is_one(self) -> (r: bool)
        requires
            self.inv(),
        ensures
            r == (self.num_s() == 1 && self.den_s() == 1),
    {
        self.num == 1 && self.den == 1
    }

    /// Sign: -1, 0, or 1.
    pub fn signum(self) -> (r: i64)
        requires
            self.inv(),
        ensures
            r == 1 <==> self.num_s() > 0,
            r == 0 <==> self.num_s() == 0,
            r == -1 <==> self.num_s() < 0,
    {
        if self.num > 0 {
            1
        } else if self.num == 0 {
            0
        } else {
            -1
        }
    }

    /// Is `0 <= self <= 1`? (The engine's constant belief-mass check.)
    pub fn in_unit_interval(self) -> (r: bool)
        requires
            self.inv(),
        ensures
            r == self.in_unit_interval_s(),
    {
        0 <= self.num && self.num <= self.den
    }

    /// Exact minimum.
    pub fn min(self, rhs: Q) -> (r: Q)
        requires
            self.inv(),
            rhs.inv(),
        ensures
            r.inv(),
            r == if q_le(self, rhs) { self } else { rhs },
    {
        if self.le(rhs) {
            self
        } else {
            rhs
        }
    }

    /// Exact maximum.
    pub fn max(self, rhs: Q) -> (r: Q)
        requires
            self.inv(),
            rhs.inv(),
        ensures
            r.inv(),
            r == if q_le(rhs, self) { self } else { rhs },
    {
        if self.le(rhs) && !rhs.le(self) {
            rhs
        } else {
            self
        }
    }

    /// Exact clamp; `lo <= hi` is a precondition.
    pub fn clamp(self, lo: Q, hi: Q) -> (r: Q)
        requires
            self.inv(),
            lo.inv(),
            hi.inv(),
            q_le(lo, hi),
        ensures
            r.inv(),
            q_le(lo, r),
            q_le(r, hi),
            q_le(lo, self) && q_le(self, hi) ==> r == self,
    {
        if self.lt(lo) {
            lo
        } else if hi.lt(self) {
            hi
        } else {
            self
        }
    }
}

// ---------------------------------------------------------------------------
// The ghost order is a total order (V6 component)
// ---------------------------------------------------------------------------

/// Reflexivity of the ghost order.
pub proof fn lemma_q_le_refl(a: Q)
    ensures
        q_le(a, a),
{
}

/// Totality of the ghost order.
pub proof fn lemma_q_le_total(a: Q, b: Q)
    ensures
        q_le(a, b) || q_le(b, a),
{
}

/// Antisymmetry (up to canonical uniqueness: mutual `<=` gives identity).
pub proof fn lemma_q_le_antisymm(a: Q, b: Q)
    requires
        a.inv(),
        b.inv(),
        q_le(a, b),
        q_le(b, a),
    ensures
        a == b,
{
    lemma_canonical_unique(a, b);
}

/// Transitivity of the ghost order.
pub proof fn lemma_q_le_trans(a: Q, b: Q, c: Q)
    requires
        a.den_s() > 0,
        b.den_s() > 0,
        c.den_s() > 0,
        q_le(a, b),
        q_le(b, c),
    ensures
        q_le(a, c),
{
    assert(a.num_s() * c.den_s() <= c.num_s() * a.den_s()) by (nonlinear_arith)
        requires
            a.num_s() * b.den_s() <= b.num_s() * a.den_s(),
            b.num_s() * c.den_s() <= c.num_s() * b.den_s(),
            a.den_s() > 0,
            b.den_s() > 0,
            c.den_s() > 0;
}

} // verus!
