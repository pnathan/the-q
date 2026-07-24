//! N-ary helpers (spec §2.5): left-to-right binary folds, so each step
//! inherits the same V2 overflow-safety and R1-R4 rounding contract as the
//! underlying binary op -- no separate overflow analysis needed. After `k`
//! elements the accumulated rounding error is bounded by `k * 2^-60`
//! (spec §4 point 2; `tests/property.rs` checks this against the
//! `malachite-q` oracle for long fold chains).

use crate::ops::{add, div, mul};
use crate::q::Q;

pub fn sum(xs: &[Q]) -> Q {
    xs.iter().fold(Q::zero(), |acc, &x| add(acc, x))
}

pub fn product(xs: &[Q]) -> Q {
    xs.iter().fold(Q::one(), |acc, &x| mul(acc, x))
}

/// `sum(value * weight) / sum(weight)` over `(value, weight)` pairs.
/// `None` if the weights sum to zero (undefined mean, mirrors [`div`]'s
/// zero-divisor precondition rather than panicking on it here since the
/// all-zero-weights case is a normal, expected input shape).
pub fn weighted_mean(pairs: &[(Q, Q)]) -> Option<Q> {
    let weighted_sum = pairs.iter().fold(Q::zero(), |acc, &(value, weight)| {
        add(acc, mul(value, weight))
    });
    let weight_sum = pairs
        .iter()
        .fold(Q::zero(), |acc, &(_, weight)| add(acc, weight));
    if weight_sum.is_zero() {
        None
    } else {
        Some(div(weighted_sum, weight_sum))
    }
}
