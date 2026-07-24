//! `QI`: a directed-rounding interval type over `Q` (spec §6/M6, stretch).
//!
//! `QI { lo, hi }` (`lo <= hi`) brackets an exact rational value: every op
//! computes `lo` with [`Dir::Down`] and `hi` with [`Dir::Up`], so the true
//! exact result of the corresponding `Q` computation is always within
//! `[lo, hi]`, no matter how rounding landed on either end (spec's R2,
//! generalized: an interval computed this way is a sound enclosure, not
//! just "close within `2^-60`"). This is the "future interval layer" the
//! `Dir` parameter on `from_f64_dir`/rounding was explicitly designed to
//! enable (spec §3) -- no new rounding-primitive work was needed, only
//! plumbing `Dir` through to each op (see `ops::{add,sub,mul,div}_dir`).
//!
//! Multiplication and division use the standard interval-arithmetic
//! "four corners" / reciprocal-interval constructions; both are proved
//! sound by construction here via down/up rounding at each corner, not
//! separately verified in Verus (out of scope for this pass -- see
//! `TRUSTED.md`).

use crate::ops::{add_dir, mul_dir, sub_dir};
use crate::q::Q;
use crate::rounding::Dir;

/// A sound enclosure `[lo, hi]` of an exact rational value, `lo <= hi`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct QI {
    lo: Q,
    hi: Q,
}

impl QI {
    /// `None` if `lo > hi`.
    pub fn new(lo: Q, hi: Q) -> Option<QI> {
        if lo <= hi {
            Some(QI { lo, hi })
        } else {
            None
        }
    }

    /// The degenerate interval `[q, q]`.
    pub fn point(q: Q) -> QI {
        QI { lo: q, hi: q }
    }

    pub fn lo(&self) -> Q {
        self.lo
    }

    pub fn hi(&self) -> Q {
        self.hi
    }

    pub fn contains(&self, q: Q) -> bool {
        self.lo <= q && q <= self.hi
    }

    /// `hi - lo` (`Nearest`-rounded like any other `Q` subtraction -- the
    /// width itself isn't required to bracket anything, so no directedness
    /// is needed here).
    pub fn width(&self) -> Q {
        crate::ops::sub(self.hi, self.lo)
    }

    /// `[from_f64_dir(v, Down), from_f64_dir(v, Up)]`. `None` under the same
    /// conditions `from_f64_dir` returns `None` (non-finite, or magnitude
    /// beyond what fits `i128`'s exact `2^exp` decomposition).
    pub fn from_f64(v: f64) -> Option<QI> {
        let lo = crate::convert::from_f64_dir(v, Dir::Down)?;
        let hi = crate::convert::from_f64_dir(v, Dir::Up)?;
        Some(QI { lo, hi })
    }
}

/// `add` is monotone in both operands, so the corner-rounded sum of the
/// endpoints already brackets every value in between.
pub fn add(a: QI, b: QI) -> QI {
    QI {
        lo: add_dir(a.lo, b.lo, Dir::Down),
        hi: add_dir(a.hi, b.hi, Dir::Up),
    }
}

/// `a - b` is monotone increasing in `a` and decreasing in `b`.
pub fn sub(a: QI, b: QI) -> QI {
    QI {
        lo: sub_dir(a.lo, b.hi, Dir::Down),
        hi: sub_dir(a.hi, b.lo, Dir::Up),
    }
}

pub fn neg(a: QI) -> QI {
    QI {
        lo: crate::ops::neg(a.hi),
        hi: crate::ops::neg(a.lo),
    }
}

/// Standard "four corners" interval multiplication: the exact product's
/// extrema over `[a.lo,a.hi] x [b.lo,b.hi]` are always attained at one of
/// the four corner pairs (regardless of sign), so rounding each corner
/// down/up and taking the min/max brackets the true result.
pub fn mul(a: QI, b: QI) -> QI {
    let corners_lo = [
        mul_dir(a.lo, b.lo, Dir::Down),
        mul_dir(a.lo, b.hi, Dir::Down),
        mul_dir(a.hi, b.lo, Dir::Down),
        mul_dir(a.hi, b.hi, Dir::Down),
    ];
    let corners_hi = [
        mul_dir(a.lo, b.lo, Dir::Up),
        mul_dir(a.lo, b.hi, Dir::Up),
        mul_dir(a.hi, b.lo, Dir::Up),
        mul_dir(a.hi, b.hi, Dir::Up),
    ];
    let lo = corners_lo.into_iter().min().unwrap();
    let hi = corners_hi.into_iter().max().unwrap();
    QI { lo, hi }
}

/// `[1/b.hi, 1/b.lo]`, valid whenever `b` doesn't contain (or touch) zero:
/// `recip` is strictly decreasing on each of `(-inf, 0)` and `(0, +inf)`
/// separately, so (since `b` is entirely on one side) the max of `1/x`
/// over `b` is at `x = b.lo` and the min at `x = b.hi`. `recip` on `Q` is
/// always exact (spec §2.2), so this needs no directed rounding of its own.
fn recip_interval(b: QI) -> Option<QI> {
    if b.contains(Q::zero()) {
        return None;
    }
    Some(QI {
        lo: crate::ops::recip(b.hi),
        hi: crate::ops::recip(b.lo),
    })
}

/// `None` if `b` contains (or touches) zero -- "denominator bounded away
/// from 0", per the spec's V7 framing.
pub fn div(a: QI, b: QI) -> Option<QI> {
    Some(mul(a, recip_interval(b)?))
}

pub fn min(a: QI, b: QI) -> QI {
    QI {
        lo: crate::ops::min(a.lo, b.lo),
        hi: crate::ops::min(a.hi, b.hi),
    }
}

pub fn max(a: QI, b: QI) -> QI {
    QI {
        lo: crate::ops::max(a.lo, b.lo),
        hi: crate::ops::max(a.hi, b.hi),
    }
}
