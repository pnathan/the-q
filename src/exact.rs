//! [`Exact`], a [`Rat`] wrapper whose arithmetic only ever returns a value
//! that equals the true, unrounded result — or reports that it cannot.
//!
//! `Rat::add`/`sub`/`mul`/`div` round silently once the exact result no
//! longer fits the budget. On the exact path (no rounding at any step),
//! `add` and `mul` are proven associative and distributive, and `add`/`mul`
//! (with a nonnegative second factor) are proven monotone (`src/laws.rs`);
//! off that path none of the three is guaranteed in general (`README.md`).
//! `Exact` turns "did this operation leave the exact path?" into an explicit
//! failure instead of a silent, unguaranteed answer, and the theorems below
//! recover each property exactly when every operation involved succeeded.

use verus_builtin_macros::verus;

#[allow(unused_imports)]
use verus_builtin::*;
#[allow(unused_imports)]
use vstd::prelude::*;

#[allow(unused_imports)]
use crate::model::*;
#[allow(unused_imports)]
use crate::q::*;
use crate::types::Rat;

verus! {

/// A [`Rat`] wrapper whose `add`/`sub`/`mul`/`div` succeed only when the
/// result needs no rounding.
///
/// ```compile_fail
/// use the_q::{Exact, Rat};
/// let _ = Exact { value: Rat::one() };
/// ```
///
/// ```compile_fail
/// use the_q::{Exact, Rat};
/// let mut e = Exact::new(Rat::one());
/// e.value = Rat::zero();
/// ```
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Exact {
    pub(crate) value: Rat,
}

impl Exact {
    /// The wrapped value, in specifications.
    pub closed spec fn spec_value(self) -> Rat {
        self.value
    }

    /// The type invariant: the wrapped [`Rat`] is well-formed. `Exact` adds
    /// no invariant of its own; exactness is a property of *operations*, not
    /// of a value in isolation.
    pub open spec fn wf(self) -> bool {
        self.spec_value().wf()
    }

    /// `r` denotes the exact sum `a + b`.
    pub open spec fn spec_is_sum(r: Exact, a: Exact, b: Exact) -> bool {
        q_is(r.spec_value(), add_n(a.spec_value(), b.spec_value()), prod_d(a.spec_value(), b.spec_value()))
    }

    /// `r` denotes the exact difference `a - b`.
    pub open spec fn spec_is_difference(r: Exact, a: Exact, b: Exact) -> bool {
        q_is(r.spec_value(), sub_n(a.spec_value(), b.spec_value()), prod_d(a.spec_value(), b.spec_value()))
    }

    /// `r` denotes the exact product `a * b`.
    pub open spec fn spec_is_product(r: Exact, a: Exact, b: Exact) -> bool {
        q_is(r.spec_value(), mul_n(a.spec_value(), b.spec_value()), prod_d(a.spec_value(), b.spec_value()))
    }

    /// `r` denotes the exact quotient `a / b`.
    pub open spec fn spec_is_quotient(r: Exact, a: Exact, b: Exact) -> bool {
        q_is(r.spec_value(), div_n(a.spec_value(), b.spec_value()), div_d(a.spec_value(), b.spec_value()))
    }

    /// Two `Exact` wrapping the same value are the same value.
    pub proof fn lemma_extensional(a: Exact, b: Exact)
        requires
            a.spec_value() == b.spec_value(),
        ensures
            a == b,
    {
        reveal(Exact::spec_value);
    }

    /// Wraps an already-computed [`Rat`]. Always exact: it denotes itself.
    pub fn new(value: Rat) -> (r: Exact)
        requires
            value.wf(),
        ensures
            r.wf(),
            r.spec_value() == value,
    {
        Exact { value }
    }

    /// The wrapped value.
    pub fn value(&self) -> (r: Rat)
        ensures
            r == self.spec_value(),
    {
        proof {
            reveal(Exact::spec_value);
        }
        self.value
    }

    /// Whether the wrapped value is nonnegative.
    pub fn is_nonneg(&self) -> (r: bool)
        requires
            self.wf(),
        ensures
            r <==> self.spec_value().n() >= 0,
    {
        proof {
            reveal(Exact::spec_value);
        }
        self.value.numerator() >= 0
    }

    /// `a <= b`.
    pub fn le(a: Exact, b: Exact) -> (r: bool)
        requires
            a.wf(),
            b.wf(),
        ensures
            r <==> q_le(a.spec_value(), b.spec_value()),
    {
        proof {
            reveal(Exact::spec_value);
        }
        Rat::le(a.value, b.value)
    }

    /// `a + b`, or `None` if the exact sum needs rounding.
    pub fn checked_add(a: Exact, b: Exact) -> (r: Option<Exact>)
        requires
            a.wf(),
            b.wf(),
        ensures
            r.is_some() <==> exact_path(
                add_n(a.spec_value(), b.spec_value()),
                prod_d(a.spec_value(), b.spec_value()),
            ),
            r.is_some() ==> r.unwrap().wf(),
            r.is_some() ==> Exact::spec_is_sum(r.unwrap(), a, b),
    {
        proof {
            reveal(Exact::spec_value);
            lemma_op_widths(a.value, b.value);
            crate::model::lemma_pow2_126();
        }
        if crate::round::exact_path_exec(add_n_exec(a.value, b.value), prod_d_exec(a.value, b.value)) {
            Some(Exact { value: Rat::add(a.value, b.value) })
        } else {
            None
        }
    }

    /// `a - b`, or `None` if the exact difference needs rounding.
    pub fn checked_sub(a: Exact, b: Exact) -> (r: Option<Exact>)
        requires
            a.wf(),
            b.wf(),
        ensures
            r.is_some() <==> exact_path(
                sub_n(a.spec_value(), b.spec_value()),
                prod_d(a.spec_value(), b.spec_value()),
            ),
            r.is_some() ==> r.unwrap().wf(),
            r.is_some() ==> Exact::spec_is_difference(r.unwrap(), a, b),
    {
        proof {
            reveal(Exact::spec_value);
            lemma_op_widths(a.value, b.value);
            crate::model::lemma_pow2_126();
        }
        if crate::round::exact_path_exec(sub_n_exec(a.value, b.value), prod_d_exec(a.value, b.value)) {
            Some(Exact { value: Rat::sub(a.value, b.value) })
        } else {
            None
        }
    }

    /// `a * b`, or `None` if the exact product needs rounding.
    pub fn checked_mul(a: Exact, b: Exact) -> (r: Option<Exact>)
        requires
            a.wf(),
            b.wf(),
        ensures
            r.is_some() <==> exact_path(
                mul_n(a.spec_value(), b.spec_value()),
                prod_d(a.spec_value(), b.spec_value()),
            ),
            r.is_some() ==> r.unwrap().wf(),
            r.is_some() ==> Exact::spec_is_product(r.unwrap(), a, b),
    {
        proof {
            reveal(Exact::spec_value);
            lemma_op_widths(a.value, b.value);
            crate::model::lemma_pow2_126();
        }
        if crate::round::exact_path_exec(mul_n_exec(a.value, b.value), prod_d_exec(a.value, b.value)) {
            Some(Exact { value: Rat::mul(a.value, b.value) })
        } else {
            None
        }
    }

    /// `a / b`, or `None` if `b` is zero or the exact quotient needs rounding.
    pub fn checked_div(a: Exact, b: Exact) -> (r: Option<Exact>)
        requires
            a.wf(),
            b.wf(),
        ensures
            b.spec_value().n() == 0 ==> r.is_none(),
            b.spec_value().n() != 0 ==> (r.is_some() <==> exact_path(
                div_n(a.spec_value(), b.spec_value()),
                div_d(a.spec_value(), b.spec_value()),
            )),
            r.is_some() ==> b.spec_value().n() != 0,
            r.is_some() ==> r.unwrap().wf(),
            r.is_some() ==> Exact::spec_is_quotient(r.unwrap(), a, b),
    {
        proof {
            reveal(Exact::spec_value);
        }
        if b.value.numerator() == 0 {
            return None;
        }
        proof {
            lemma_op_widths(a.value, b.value);
            crate::model::lemma_pow2_126();
            assert(b.value.n() > 0 ==> a.value.d() * b.value.n() > 0) by (nonlinear_arith)
                requires
                    a.value.d() > 0,
            ;
            assert(b.value.n() < 0 ==> a.value.d() * b.value.n() < 0) by (nonlinear_arith)
                requires
                    a.value.d() > 0,
            ;
        }
        if crate::round::exact_path_exec(div_n_exec(a.value, b.value), div_d_exec(a.value, b.value)) {
            Some(Exact { value: Rat::div(a.value, b.value) })
        } else {
            None
        }
    }
}

// ---------------------------------------------------------------------------
// Theorems: associativity, distributivity, and monotonicity, each holding
// exactly when every `Exact` operation it names actually succeeded.
// ---------------------------------------------------------------------------

/// If `(a+b)+c` and `a+(b+c)` both succeeded exactly, they are equal.
pub proof fn theorem_exact_add_associative(
    a: Exact,
    b: Exact,
    c: Exact,
    ab: Exact,
    bc: Exact,
    left: Exact,
    right: Exact,
)
    requires
        a.wf(),
        b.wf(),
        c.wf(),
        ab.wf(),
        bc.wf(),
        left.wf(),
        right.wf(),
        Exact::spec_is_sum(ab, a, b),
        Exact::spec_is_sum(bc, b, c),
        Exact::spec_is_sum(left, ab, c),
        Exact::spec_is_sum(right, a, bc),
    ensures
        left == right,
{
    crate::laws::lemma_add_assoc_exact_values(
        a.spec_value(),
        b.spec_value(),
        c.spec_value(),
        ab.spec_value(),
        bc.spec_value(),
        left.spec_value(),
        right.spec_value(),
    );
    crate::laws::lemma_canonical_eq(left.spec_value(), right.spec_value());
    Exact::lemma_extensional(left, right);
}

/// If `(a*b)*c` and `a*(b*c)` both succeeded exactly, they are equal.
pub proof fn theorem_exact_mul_associative(
    a: Exact,
    b: Exact,
    c: Exact,
    ab: Exact,
    bc: Exact,
    left: Exact,
    right: Exact,
)
    requires
        a.wf(),
        b.wf(),
        c.wf(),
        ab.wf(),
        bc.wf(),
        left.wf(),
        right.wf(),
        Exact::spec_is_product(ab, a, b),
        Exact::spec_is_product(bc, b, c),
        Exact::spec_is_product(left, ab, c),
        Exact::spec_is_product(right, a, bc),
    ensures
        left == right,
{
    crate::laws::theorem_mul_associative_exact(
        a.spec_value(),
        b.spec_value(),
        c.spec_value(),
        ab.spec_value(),
        bc.spec_value(),
        left.spec_value(),
        right.spec_value(),
    );
    crate::laws::lemma_canonical_eq(left.spec_value(), right.spec_value());
    Exact::lemma_extensional(left, right);
}

/// If `bc = b+c`, `lhs = a*bc`, `ab = a*b`, `ac = a*c`, and `rhs = ab+ac` all
/// succeeded exactly, then `lhs == rhs`: `a*(b+c) == a*b + a*c`.
pub proof fn theorem_exact_distributive(
    a: Exact,
    b: Exact,
    c: Exact,
    bc: Exact,
    lhs: Exact,
    ab: Exact,
    ac: Exact,
    rhs: Exact,
)
    requires
        a.wf(),
        b.wf(),
        c.wf(),
        bc.wf(),
        lhs.wf(),
        ab.wf(),
        ac.wf(),
        rhs.wf(),
        Exact::spec_is_sum(bc, b, c),
        Exact::spec_is_product(lhs, a, bc),
        Exact::spec_is_product(ab, a, b),
        Exact::spec_is_product(ac, a, c),
        Exact::spec_is_sum(rhs, ab, ac),
    ensures
        lhs == rhs,
{
    crate::laws::theorem_distributive_exact(
        a.spec_value(),
        b.spec_value(),
        c.spec_value(),
        bc.spec_value(),
        lhs.spec_value(),
        ab.spec_value(),
        ac.spec_value(),
        rhs.spec_value(),
    );
    crate::laws::lemma_canonical_eq(lhs.spec_value(), rhs.spec_value());
    Exact::lemma_extensional(lhs, rhs);
}

/// If `a <= b` and `ac = a+c`, `bc = b+c` both succeeded exactly, then
/// `ac <= bc`.
pub proof fn theorem_exact_add_monotone(a: Exact, b: Exact, c: Exact, ac: Exact, bc: Exact)
    requires
        a.wf(),
        b.wf(),
        c.wf(),
        ac.wf(),
        bc.wf(),
        q_le(a.spec_value(), b.spec_value()),
        Exact::spec_is_sum(ac, a, c),
        Exact::spec_is_sum(bc, b, c),
    ensures
        q_le(ac.spec_value(), bc.spec_value()),
{
    let av = a.spec_value();
    let bv = b.spec_value();
    let cv = c.spec_value();
    let x = ac.spec_value();
    let y = bc.spec_value();
    crate::laws::theorem_add_monotone_exact(av, bv, cv);
    crate::q::lemma_op_widths(av, cv);
    crate::q::lemma_op_widths(bv, cv);
    crate::interval::lemma_frac_chain_le(
        x.n(),
        x.d(),
        add_n(av, cv),
        prod_d(av, cv),
        add_n(bv, cv),
        prod_d(bv, cv),
        y.n(),
        y.d(),
    );
}

/// If `a <= b`, `c >= 0`, and `ac = a*c`, `bc = b*c` both succeeded exactly,
/// then `ac <= bc`.
pub proof fn theorem_exact_mul_monotone_nonneg(a: Exact, b: Exact, c: Exact, ac: Exact, bc: Exact)
    requires
        a.wf(),
        b.wf(),
        c.wf(),
        ac.wf(),
        bc.wf(),
        q_le(a.spec_value(), b.spec_value()),
        c.spec_value().n() >= 0,
        Exact::spec_is_product(ac, a, c),
        Exact::spec_is_product(bc, b, c),
    ensures
        q_le(ac.spec_value(), bc.spec_value()),
{
    let av = a.spec_value();
    let bv = b.spec_value();
    let cv = c.spec_value();
    let x = ac.spec_value();
    let y = bc.spec_value();
    crate::laws::theorem_mul_monotone_nonneg_exact(av, bv, cv);
    crate::q::lemma_op_widths(av, cv);
    crate::q::lemma_op_widths(bv, cv);
    crate::interval::lemma_frac_chain_le(
        x.n(),
        x.d(),
        mul_n(av, cv),
        prod_d(av, cv),
        mul_n(bv, cv),
        prod_d(bv, cv),
        y.n(),
        y.d(),
    );
}

} // verus!

// ---------------------------------------------------------------------------
// The ergonomic `Result` layer. Plain Rust, not proof-carrying: it only
// re-packages the verified `checked_*` primitives above into a friendlier
// error type, and (for `div`) checks the zero divisor before calling in so
// the two failure causes are distinguishable.
// ---------------------------------------------------------------------------

/// Why an [`Exact`] operation could not return a value.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum ExactError {
    /// The exact result does not fit the budget: it would have to round.
    Inexact,
    /// The divisor was zero.
    DivisionByZero,
}

#[cfg_attr(verus_keep_ghost, verifier::external)]
impl core::fmt::Display for ExactError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(match self {
            ExactError::Inexact => "the-q: exact result would need rounding",
            ExactError::DivisionByZero => "the-q: division by zero",
        })
    }
}

#[cfg_attr(verus_keep_ghost, verifier::external)]
impl std::error::Error for ExactError {}

#[cfg_attr(verus_keep_ghost, verifier::external)]
impl Exact {
    /// `a + b`, or [`ExactError::Inexact`] if the exact sum needs rounding.
    pub fn add(a: Exact, b: Exact) -> Result<Exact, ExactError> {
        Exact::checked_add(a, b).ok_or(ExactError::Inexact)
    }

    /// `a - b`, or [`ExactError::Inexact`] if the exact difference needs
    /// rounding.
    pub fn sub(a: Exact, b: Exact) -> Result<Exact, ExactError> {
        Exact::checked_sub(a, b).ok_or(ExactError::Inexact)
    }

    /// `a * b`, or [`ExactError::Inexact`] if the exact product needs
    /// rounding.
    pub fn mul(a: Exact, b: Exact) -> Result<Exact, ExactError> {
        Exact::checked_mul(a, b).ok_or(ExactError::Inexact)
    }

    /// `a / b`, or [`ExactError::DivisionByZero`] / [`ExactError::Inexact`].
    pub fn div(a: Exact, b: Exact) -> Result<Exact, ExactError> {
        if b.value().numerator() == 0 {
            return Err(ExactError::DivisionByZero);
        }
        Exact::checked_div(a, b).ok_or(ExactError::Inexact)
    }
}
