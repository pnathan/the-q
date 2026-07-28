//! Exact decimal ingestion (the engine's primary input path) and n-ary
//! fold helpers.

use vstd::prelude::*;

#[allow(unused_imports)]
use crate::accumulate::*;
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
#[allow(unused_imports)]
use vstd::arithmetic::power2::*;

verus! {

/// `10^e` over nat.
pub open spec fn ten_pow(e: nat) -> nat
    decreases e,
{
    if e == 0 {
        1
    } else {
        10 * ten_pow((e - 1) as nat)
    }
}

/// Exec `10^e`, `e <= 18` (so the result is below the I2 budget).
fn ten_pow_u128(e: u32) -> (r: u128)
    requires
        e <= 18,
    ensures
        r as nat == ten_pow(e as nat),
        r >= 1,
        r <= 1_000_000_000_000_000_000,
{
    let mut r: u128 = 1;
    let mut i: u32 = 0;
    proof {
        assert(ten_pow(0) == 1);
    }
    while i < e
        invariant
            i <= e,
            e <= 18,
            r as nat == ten_pow(i as nat),
            r >= 1,
        decreases e - i,
    {
        proof {
            lemma_ten_pow_le(i as nat, 17);
            assert(ten_pow(17) == 100_000_000_000_000_000) by (compute);
        }
        r = r * 10;
        i = i + 1;
    }
    proof {
        lemma_ten_pow_le(e as nat, 18);
        assert(ten_pow(18) == 1_000_000_000_000_000_000) by (compute);
    }
    r
}

/// `ten_pow` is monotone.
proof fn lemma_ten_pow_le(a: nat, b: nat)
    requires
        a <= b,
    ensures
        ten_pow(a) <= ten_pow(b),
        ten_pow(a) >= 1,
    decreases b,
{
    if b == 0 {
    } else if a == b {
        lemma_ten_pow_le((b - 1) as nat, (b - 1) as nat);
        assert(ten_pow(b) == 10 * ten_pow((b - 1) as nat));
        assert(ten_pow(b) >= ten_pow((b - 1) as nat)) by (nonlinear_arith)
            requires ten_pow((b - 1) as nat) >= 1, ten_pow(b) == 10 * ten_pow((b - 1) as nat);
    } else {
        lemma_ten_pow_le(a, (b - 1) as nat);
        assert(ten_pow(b) >= ten_pow((b - 1) as nat)) by (nonlinear_arith)
            requires ten_pow((b - 1) as nat) >= 1, ten_pow(b) == 10 * ten_pow((b - 1) as nat);
    }
}

impl Q {
    /// Exact decimal input: `from_decimal(85, 2) == 0.85` exactly.
    ///
    /// `None` iff `dec_places > 18` or the reduced value exceeds the I2
    /// budget (possible only for `|mantissa| > 2^62 - 1` after reduction).
    /// Never rounds.
    pub fn from_decimal(mantissa: i64, dec_places: u8) -> (r: Option<Q>)
        ensures
            dec_places > 18 ==> r is None,
            dec_places <= 18 ==> (r is Some <==> new_fits(
                mantissa as int,
                ten_pow(dec_places as nat) as int,
            )),
            r is Some ==> {
                let q = r.unwrap();
                &&& q.inv()
                &&& q.num_s() * (ten_pow(dec_places as nat) as int) == (mantissa as int)
                    * q.den_s()
            },
    {
        if dec_places > 18 {
            return None;
        }
        let den = ten_pow_u128(dec_places as u32);
        let neg = mantissa < 0;
        let un = crate::q::abs_i64_u128(mantissa);
        let r = crate::q::make_canonical(neg, un, den);
        proof {
            let g = gcd(un as nat, den as nat);
            let rn = (un as nat / g) as int;
            let rd = (den as nat / g) as int;
            if r is Some {
                let q = r.unwrap();
                crate::round::lemma_signed_value(
                    q.num_s(), q.den_s(), g as int, rn, rd, neg, un as int, den as int);
                assert(abs_i(mantissa as int) == un as int);
                if neg {
                    assert(q.num_s() * (den as int) == (mantissa as int) * q.den_s());
                } else {
                    assert(q.num_s() * (den as int) == (mantissa as int) * q.den_s());
                }
            }
            assert(abs_i(ten_pow(dec_places as nat) as int) == den as int);
        }
        r
    }

    // -----------------------------------------------------------------------
    // n-ary helpers (fixed left-to-right binary folds, so V2 safety and
    // determinism are inherited from the binary ops)
    // -----------------------------------------------------------------------

    /// Left fold of `add` over a slice (Nearest). Deterministic: fixed
    /// evaluation order. Exact whenever every partial sum fits the budget
    /// (R1). The V8 ensures: whenever the exact partial sums admit a bound
    /// `w`, the result is within `2*k*w / 2^60` (i.e. `k*w*2^-59`) of the
    /// exact sum (see `crate::accumulate`).
    pub fn sum(xs: &[Q]) -> (r: Q)
        requires
            forall|i: int| 0 <= i < xs@.len() ==> #[trigger] xs@[i].inv(),
        ensures
            r.inv(),
            forall|w: int|
                (w >= 1 && 4 * w <= max_mag() && xs@.len() <= fold_len_cap()
                    && #[trigger] prefix_add_bounded(xs@, w))
                    ==> frac_close(
                        r.num_s(), r.den_s(),
                        exact_fold_add(xs@).0, exact_fold_add(xs@).1,
                        2 * (xs@.len() as int) * w, pow2(60) as int),
    {
        let mut acc = Q::zero();
        let ghost mut accs: Seq<Q> = seq![acc];
        let mut i: usize = 0;
        while i < xs.len()
            invariant
                acc.inv(),
                i <= xs@.len(),
                forall|j: int| 0 <= j < xs@.len() ==> #[trigger] xs@[j].inv(),
                accs.len() == i + 1,
                accs[0].inv() && accs[0].num_s() == 0 && accs[0].den_s() == 1,
                accs[i as int] == acc,
                forall|j: int| 0 <= j < i ==> #[trigger] add_step_ok(xs@, accs, j),
            decreases xs@.len() - i,
        {
            let ghost accs_old = accs;
            let prev = acc;
            acc = prev.add(xs[i]);
            proof {
                accs = accs.push(acc);
                assert(accs[i as int] == prev);
                assert(accs[i as int + 1] == acc);
                assert(add_step_ok(xs@, accs, i as int));
                assert forall|j: int| 0 <= j < i + 1 implies #[trigger] add_step_ok(
                    xs@, accs, j) by {
                    if j < i {
                        assert(add_step_ok(xs@, accs_old, j));
                        assert(accs[j] == accs_old[j] && accs[j + 1] == accs_old[j + 1]);
                    }
                }
            }
            i = i + 1;
        }
        proof {
            assert(add_chain_ok(xs@, accs));
            assert forall|w: int|
                (w >= 1 && 4 * w <= max_mag() && xs@.len() <= fold_len_cap()
                    && #[trigger] prefix_add_bounded(xs@, w))
                    implies frac_close(
                        acc.num_s(), acc.den_s(),
                        exact_fold_add(xs@).0, exact_fold_add(xs@).1,
                        2 * (xs@.len() as int) * w, pow2(60) as int) by {
                theorem_fold_add_error(xs@, accs, w);
            }
        }
        acc
    }

    /// Left fold of `mul` over a slice (Nearest); see `sum`. The V8
    /// ensures: for unit-interval elements (the engine's case) the result
    /// is within `2*k / 2^60` (i.e. `k*2^-59`) of the exact product.
    pub fn product(xs: &[Q]) -> (r: Q)
        requires
            forall|i: int| 0 <= i < xs@.len() ==> #[trigger] xs@[i].inv(),
        ensures
            r.inv(),
            all_unit(xs@) && xs@.len() <= fold_len_cap() ==> frac_close(
                r.num_s(), r.den_s(),
                exact_fold_mul(xs@).0, exact_fold_mul(xs@).1,
                2 * (xs@.len() as int), pow2(60) as int),
    {
        let mut acc = Q::one();
        let ghost mut accs: Seq<Q> = seq![acc];
        let mut i: usize = 0;
        while i < xs.len()
            invariant
                acc.inv(),
                i <= xs@.len(),
                forall|j: int| 0 <= j < xs@.len() ==> #[trigger] xs@[j].inv(),
                accs.len() == i + 1,
                accs[0].inv() && accs[0].num_s() == 1 && accs[0].den_s() == 1,
                accs[i as int] == acc,
                forall|j: int| 0 <= j < i ==> #[trigger] mul_step_ok(xs@, accs, j),
            decreases xs@.len() - i,
        {
            let ghost accs_old = accs;
            let prev = acc;
            acc = prev.mul(xs[i]);
            proof {
                accs = accs.push(acc);
                assert(accs[i as int] == prev);
                assert(accs[i as int + 1] == acc);
                assert(mul_step_ok(xs@, accs, i as int));
                assert forall|j: int| 0 <= j < i + 1 implies #[trigger] mul_step_ok(
                    xs@, accs, j) by {
                    if j < i {
                        assert(mul_step_ok(xs@, accs_old, j));
                        assert(accs[j] == accs_old[j] && accs[j + 1] == accs_old[j + 1]);
                    }
                }
            }
            i = i + 1;
        }
        proof {
            assert(mul_chain_ok(xs@, accs));
            if all_unit(xs@) && xs@.len() <= fold_len_cap() {
                theorem_fold_mul_error(xs@, accs);
            }
        }
        acc
    }

    /// Integer power by repeated multiplication (Nearest), left-to-right —
    /// the "trivially cheap" u32-exponent form permitted by spec section 2.6.
    /// For unit-interval bases the accumulated error follows the product
    /// fold bound (`crate::accumulate::theorem_fold_mul_error`).
    pub fn int_pow(self, e: u32) -> (r: Q)
        requires
            self.inv(),
        ensures
            r.inv(),
    {
        let mut r = Q::one();
        let mut i: u32 = 0;
        while i < e
            invariant
                r.inv(),
                self.inv(),
                i <= e,
            decreases e - i,
        {
            r = r.mul(self);
            i = i + 1;
        }
        r
    }

    /// Weighted mean `sum(w_i * x_i) / sum(w_i)` over `(value, weight)`
    /// pairs, as fixed-order folds; `None` if the weight sum is zero.
    /// The ABF formula shape from the consuming engine.
    pub fn weighted_mean(xs: &[(Q, Q)]) -> (r: Option<Q>)
        requires
            forall|i: int| 0 <= i < xs@.len() ==> #[trigger] xs@[i].0.inv() && xs@[i].1.inv(),
        ensures
            r is Some ==> r.unwrap().inv(),
    {
        let mut num = Q::zero();
        let mut den = Q::zero();
        let mut i: usize = 0;
        while i < xs.len()
            invariant
                num.inv(),
                den.inv(),
                i <= xs@.len(),
                forall|j: int| 0 <= j < xs@.len() ==> #[trigger] xs@[j].0.inv() && xs@[j].1.inv(),
            decreases xs@.len() - i,
        {
            proof {
                assert(xs@[i as int].0.inv() && xs@[i as int].1.inv());
            }
            let (x, w) = xs[i];
            num = num.add(x.mul(w));
            den = den.add(w);
            i = i + 1;
        }
        if den.is_zero() {
            None
        } else {
            Some(num.div(den))
        }
    }
}

} // verus!
