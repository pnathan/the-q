//! Verified rounding to the I2 budget (obligation V4, contract R1-R4).
//!
//! Strategy: an exact result `en/ed` (from i128 intermediates) that does not
//! fit the budget after GCD reduction is snapped to a dyadic grid `k / 2^s`:
//!
//! - the scale `s` is the largest `s <= 61` with `|en| * 2^s <= MAX * ed`
//!   (so every candidate numerator fits the budget);
//! - `k` is the directed rounding of `|en| * 2^s / ed`, computed by binary
//!   search using *exact* wide comparisons (`crate::wide`) - there is no
//!   error-prone division anywhere, every step is an exact integer compare;
//! - the result `+-k / 2^s` is then canonicalized (which can only shrink it).
//!
//! Everything the caller learns is packaged in `round_char`, a *unique*
//! characterization of the result (see `lemma_round_char_unique`): this is
//! what makes determinism theorems (e.g. commutativity of `add`) provable.
//! The human-facing contract R1-R3 is derived from it in
//! `lemma_round_char_correct`; R4 (per-grid monotonicity) is
//! `lemma_mag_round_monotone`.

use vstd::prelude::*;
#[allow(unused_imports)]
use vstd::arithmetic::div_mod::*;
#[allow(unused_imports)]
use vstd::arithmetic::power2::*;

#[allow(unused_imports)]
use crate::gcd::*;
#[allow(unused_imports)]
use crate::q::*;
#[allow(unused_imports)]
use crate::specs::*;
#[allow(unused_imports)]
use crate::wide::*;

verus! {

/// Rounding direction. `Down` / `Up` are toward -inf / +inf; `Nearest`
/// breaks ties away from zero. All plain operators use `Nearest`; the
/// directed modes exist so an interval layer can bracket exactly.
#[derive(Clone, Copy, PartialEq, Eq, Structural)]
pub enum Dir {
    Down,
    Up,
    Nearest,
}

// ---------------------------------------------------------------------------
// Spec-level characterization of the rounding pipeline
// ---------------------------------------------------------------------------

/// `s` is the chosen dyadic scale for magnitude `un / ud`: the largest
/// `s <= 61` such that `un * 2^s <= MAX * ud`.
pub open spec fn is_scale(s: nat, un: int, ud: int) -> bool {
    &&& s <= 61
    &&& un * pow2(s) <= max_mag() * ud
    &&& (s < 61 ==> un * pow2((s + 1) as nat) > max_mag() * ud)
}

/// `k == floor(un * 2^s / ud)`, division-free.
pub open spec fn is_floor(k: int, s: nat, un: int, ud: int) -> bool {
    k * ud <= un * pow2(s) < (k + 1) * ud
}

/// `k == ceil(un * 2^s / ud)`, division-free.
pub open spec fn is_ceil(k: int, s: nat, un: int, ud: int) -> bool {
    (k - 1) * ud < un * pow2(s) <= k * ud
}

/// `k` is the `mdir`-rounding of the magnitude `un * 2^s / ud`.
/// `Nearest` breaks ties upward (away from zero, since this is a magnitude).
pub open spec fn is_mag_round(k: int, s: nat, un: int, ud: int, mdir: Dir) -> bool {
    match mdir {
        Dir::Down => is_floor(k, s, un, ud),
        Dir::Up => is_ceil(k, s, un, ud),
        Dir::Nearest => {
            ||| (k * ud <= un * pow2(s) && 2 * (un * pow2(s) - k * ud) < ud)
            ||| (k * ud > un * pow2(s) && 2 * (k * ud - un * pow2(s)) <= ud)
        },
    }
}

/// The direction to apply on magnitudes: rounding a negative value toward
/// -inf means rounding its magnitude up, and vice versa.
pub open spec fn mag_dir(dir: Dir, neg: bool) -> Dir {
    match dir {
        Dir::Down => if neg { Dir::Up } else { Dir::Down },
        Dir::Up => if neg { Dir::Down } else { Dir::Up },
        Dir::Nearest => Dir::Nearest,
    }
}

/// `k` is the correctly-rounded magnitude of `en / ed` at scale `s`, with
/// the direction adjusted for the sign of `en` (trigger-friendly wrapper).
pub open spec fn signed_mag_round(k: int, s: nat, en: int, ed: int, dir: Dir) -> bool {
    is_mag_round(k, s, abs_i(en), ed, mag_dir(dir, en < 0))
}

/// Full (unique) characterization of the rounded result `q` for the exact
/// fraction `en / ed` (`ed > 0`) under direction `dir`:
///
/// - R1: if the reduced exact value fits the budget, `q` is exactly it;
/// - otherwise, if `|en/ed| <= MAX`, `q` is the `dir`-rounding of `en/ed`
///   on the chosen dyadic grid;
/// - otherwise the magnitude saturates at `MAX/1` (sign preserved).
pub open spec fn round_char(q: Q, en: int, ed: int, dir: Dir) -> bool
    recommends
        ed > 0,
{
    if new_fits(en, ed) {
        q.is_frac(en, ed)
    } else if abs_i(en) <= max_mag() * ed {
        exists|s: nat, k: int|
            is_scale(s, abs_i(en), ed) && #[trigger] signed_mag_round(k, s, en, ed, dir)
                && q.num_s() * pow2(s) == (if en < 0 { -k } else { k }) * q.den_s()
    } else {
        q.num_s() == (if en < 0 { -max_mag() } else { max_mag() }) && q.den_s() == 1
    }
}

/// The human-facing rounding contract (R1, R2, R3 with B = 60), derived
/// from `round_char` by `lemma_round_char_correct`.
pub open spec fn rounds_to(q: Q, en: int, ed: int, dir: Dir) -> bool
    recommends
        ed > 0,
{
    let diff = q.num_s() * ed - en * q.den_s();
    &&& (new_fits(en, ed) ==> diff == 0)  // R1: identity on representables
    &&& (abs_i(en) <= max_mag() * ed ==> {
        // R2: directed rounding
        &&& (dir == Dir::Down ==> diff <= 0)
        &&& (dir == Dir::Up ==> diff >= 0)
        // R3: |result - x| <= 2^-60 * max(1, |x|), cross-multiplied
        &&& (abs_i(en) <= ed ==> abs_i(diff) * pow2(60) <= q.den_s() * ed)
        &&& (abs_i(en) > ed ==> abs_i(diff) * pow2(60) <= q.den_s() * abs_i(en))
    })
}

// ---------------------------------------------------------------------------
// Exec: scale selection
// ---------------------------------------------------------------------------

/// Marker for "scale s is too big": `un * 2^s > MAX * ud`.
pub open spec fn scale_fails(s: nat, un: int, ud: int) -> bool {
    un * pow2(s) > max_mag() * ud
}

/// Find the largest usable dyadic scale, or report that even `s == 0`
/// overflows the budget (`un > MAX * ud`, i.e. the value saturates).
fn choose_scale(un: u128, ud: u128) -> (r: (bool, u32))
    requires
        ud > 0,
        un < 0x2000_0000_0000_0000_0000_0000_0000_0000,  // 2^125
    ensures
        r.0 ==> is_scale(r.1 as nat, un as int, ud as int),
        !r.0 ==> un as int > max_mag() * (ud as int),
{
    let mmax: u128 = MAX_MAG as u128;
    proof {
        assert(mmax < P64) by (compute);
    }
    let mud = wide_mul(mmax, ud);
    let mut s: u32 = 61;
    loop
        invariant
            s <= 61,
            ud > 0,
            un < 0x2000_0000_0000_0000_0000_0000_0000_0000,
            wval(mud) == max_mag() * (ud as int),
            forall|j: nat| s < j <= 61 ==> #[trigger] scale_fails(j, un as int, ud as int),
        decreases s,
    {
        let t = wide_shl(un, s);
        if wide_le(t, mud) {
            proof {
                if s < 61 {
                    assert(scale_fails((s + 1) as nat, un as int, ud as int));
                }
                assert(is_scale(s as nat, un as int, ud as int));
            }
            return (true, s);
        }
        proof {
            assert(scale_fails(s as nat, un as int, ud as int));
        }
        if s == 0 {
            proof {
                assert(pow2(0) == 1) by {
                    lemma2_to64();
                }
                assert(un as int > max_mag() * (ud as int));
            }
            return (false, 0);
        }
        s = s - 1;
    }
}

// ---------------------------------------------------------------------------
// Exec: floor by binary search on exact comparisons
// ---------------------------------------------------------------------------

/// Compute `floor(un * 2^s / ud)` by binary search over `[0, MAX]`,
/// deciding each step with an exact wide comparison.
fn floor_div_wide(un: u128, ud: u128, s: u32) -> (k: u64)
    requires
        ud > 0,
        s <= 61,
        (un as int) * pow2(s as nat) <= max_mag() * (ud as int),
    ensures
        is_floor(k as int, s as nat, un as int, ud as int),
        k <= MAX_MAG as u64,
{
    let target = wide_shl(un, s);
    let mut lo: u64 = 0;
    let mut hi: u64 = MAX_MAG as u64 + 1;
    proof {
        lemma_pow2_pos(s as nat);
        assert((lo as int) * (ud as int) <= wval(target)) by (nonlinear_arith)
            requires wval(target) == (un as int) * pow2(s as nat), lo == 0, un >= 0, pow2(s as nat) > 0;
        assert(wval(target) < (hi as int) * (ud as int)) by (nonlinear_arith)
            requires
                wval(target) <= max_mag() * (ud as int),
                hi as int == max_mag() + 1,
                ud > 0;
        lemma_pow2_pos(s as nat);
    }
    while hi - lo > 1
        invariant
            lo < hi,
            hi <= MAX_MAG as u64 + 1,
            wval(target) == (un as int) * pow2(s as nat),
            ud > 0,
            (lo as int) * (ud as int) <= wval(target),
            wval(target) < (hi as int) * (ud as int),
        decreases hi - lo,
    {
        let mid = lo + (hi - lo) / 2;
        proof {
            assert(mmax_small_mult_ok(mid as int));
        }
        let p = wide_mul(mid as u128, ud);
        if wide_le(p, target) {
            lo = mid;
        } else {
            hi = mid;
        }
    }
    lo
}

/// Every candidate numerator is small enough for `wide_mul`.
spec fn mmax_small_mult_ok(k: int) -> bool {
    0 <= k < P64 as int
}

// ---------------------------------------------------------------------------
// Exec: directed rounding of a magnitude at the chosen scale
// ---------------------------------------------------------------------------

/// Round the magnitude `un / ud` onto the grid `k / 2^s` in direction
/// `mdir`, using only exact comparisons.
fn mag_round_exec(un: u128, ud: u128, s: u32, mdir: Dir) -> (k: u64)
    requires
        ud > 0,
        s <= 61,
        (un as int) * pow2(s as nat) <= max_mag() * (ud as int),
    ensures
        is_mag_round(k as int, s as nat, un as int, ud as int, mdir),
        k <= MAX_MAG as u64,
{
    let f = floor_div_wide(un, ud, s);
    let target = wide_shl(un, s);
    match mdir {
        Dir::Down => f,
        Dir::Up => {
            let p = wide_mul(f as u128, ud);
            if wide_eq(p, target) {
                proof {
                    // exact: ceil == floor
                    assert((f as int - 1) * (ud as int) < (un as int) * pow2(s as nat))
                        by (nonlinear_arith)
                        requires
                            (f as int) * (ud as int) == (un as int) * pow2(s as nat),
                            ud > 0;
                }
                f
            } else {
                proof {
                    // strict: floor < value, so ceil == floor + 1, still <= MAX
                    assert(f as int + 1 <= max_mag() && (un as int) * pow2(s as nat) <= (f as int + 1) * (ud as int))
                        by (nonlinear_arith)
                        requires
                            (f as int) * (ud as int) <= (un as int) * pow2(s as nat),
                            (f as int) * (ud as int) != (un as int) * pow2(s as nat),
                            (un as int) * pow2(s as nat) < (f as int + 1) * (ud as int),
                            (un as int) * pow2(s as nat) <= max_mag() * (ud as int),
                            ud > 0;
                }
                f + 1
            }
        },
        Dir::Nearest => {
            // Decide between f and f + 1 by comparing 2 * (un * 2^s) with
            // (2f + 1) * ud; ties go to f + 1 (away from zero).
            let a = wide_shl(un, s + 1);
            let b = wide_mul(2 * (f as u128) + 1, ud);
            proof {
                lemma_pow2_adds(s as nat, 1);
                lemma2_to64();
                assert(wval(a) == 2 * ((un as int) * pow2(s as nat))) by (nonlinear_arith)
                    requires
                        wval(a) == (un as int) * pow2((s + 1) as nat),
                        pow2((s + 1) as nat) == pow2(s as nat) * 2;
            }
            if wide_lt(a, b) {
                proof {
                    assert(2 * ((un as int) * pow2(s as nat) - (f as int) * (ud as int)) < ud as int)
                        by (nonlinear_arith)
                        requires
                            2 * ((un as int) * pow2(s as nat)) < (2 * (f as int) + 1) * (ud as int);
                }
                f
            } else {
                proof {
                    // value >= f + 1/2 > f, so f is not exact and f + 1 <= MAX
                    assert(f as int + 1 <= max_mag()
                        && (f as int + 1) * (ud as int) > (un as int) * pow2(s as nat)
                        && 2 * ((f as int + 1) * (ud as int) - (un as int) * pow2(s as nat)) <= ud as int)
                        by (nonlinear_arith)
                        requires
                            2 * ((un as int) * pow2(s as nat)) >= (2 * (f as int) + 1) * (ud as int),
                            (f as int) * (ud as int) <= (un as int) * pow2(s as nat),
                            (un as int) * pow2(s as nat) < (f as int + 1) * (ud as int),
                            (un as int) * pow2(s as nat) <= max_mag() * (ud as int),
                            ud > 0;
                }
                f + 1
            }
        },
    }
}

// ---------------------------------------------------------------------------
// Sign plumbing
// ---------------------------------------------------------------------------

/// Pushing a sign through a canonically-reduced fraction: if `q`'s fields
/// are the reduced magnitudes with `neg` applied, then `q` equals the
/// signed original as a cross-multiplication.
pub(crate) proof fn lemma_signed_value(qn: int, qd: int, g: int, rn: int, rd: int, neg: bool, un: int, ud: int)
    requires
        qn == if neg { -rn } else { rn },
        qd == rd,
        un == g * rn,
        ud == g * rd,
    ensures
        qn * ud == (if neg { -un } else { un }) * qd,
{
    if neg {
        assert((-rn) * ud == (-un) * rd) by (nonlinear_arith)
            requires un == g * rn, ud == g * rd;
    } else {
        assert(rn * ud == un * rd) by (nonlinear_arith)
            requires un == g * rn, ud == g * rd;
    }
}

// ---------------------------------------------------------------------------
// The full rounding pipeline
// ---------------------------------------------------------------------------

/// Signed exact value fed to the pipeline as (sign, magnitude, denominator).
pub open spec fn signed(neg: bool, un: int) -> int {
    if neg { -un } else { un }
}

/// Reduce-or-round: the single entry point every arithmetic op funnels
/// through. Exact (R1) whenever the reduced result fits the budget;
/// otherwise dyadic rounding per `round_char`; saturates at `+-MAX/1` when
/// even `s == 0` cannot represent the magnitude.
pub(crate) fn round_frac(neg: bool, un: u128, ud: u128, dir: Dir) -> (q: Q)
    requires
        ud > 0,
        un < 0x2000_0000_0000_0000_0000_0000_0000_0000,  // 2^125
        ud < 0x2000_0000_0000_0000_0000_0000_0000_0000,
    ensures
        q.inv(),
        round_char(q, signed(neg, un as int), ud as int, dir),
{
    let ghost en: int = signed(neg, un as int);
    proof {
        assert(abs_i(en) == un as int);
        assert(abs_i(ud as int) == ud as int);
    }
    match make_canonical(neg, un, ud) {
        Some(q) => {
            proof {
                let g = gcd(un as nat, ud as nat);
                let rn = (un as nat / g) as int;
                let rd = (ud as nat / g) as int;
                lemma_signed_value(
                    q.num_s(), q.den_s(), g as int, rn, rd, neg, un as int, ud as int);
                assert(new_fits(en, ud as int));
                assert(q.is_frac(en, ud as int));
            }
            q
        },
        None => {
            proof {
                // The reduced form does not fit; in particular un > 0
                // (a zero numerator always reduces to 0/1, which fits).
                if un == 0 {
                    lemma_small_mod(0, ud as nat);
                    assert(gcd(0, ud as nat) == gcd(ud as nat, 0));
                    lemma_div_of0(ud as int);
                    lemma_div_by_self(ud as int);
                    assert(false);
                }
                assert(!new_fits(en, ud as int));
                assert((en < 0) == neg);
            }
            let (found, s) = choose_scale(un, ud);
            if found {
                let mdir = match dir {
                    Dir::Down => if neg { Dir::Up } else { Dir::Down },
                    Dir::Up => if neg { Dir::Down } else { Dir::Up },
                    Dir::Nearest => Dir::Nearest,
                };
                proof {
                    assert(mdir == mag_dir(dir, en < 0));
                }
                let k = mag_round_exec(un, ud, s, mdir);
                let p2s = pow2_u128(s);
                proof {
                    // canonicalizing k / 2^s can only shrink the magnitudes,
                    // so it always fits
                    let g2 = gcd(k as nat, p2s as nat);
                    lemma_gcd_pos(k as nat, p2s as nat);
                    lemma_gcd_divides(k as nat, p2s as nat);
                    lemma_div_exact(g2, k as nat);
                    lemma_div_exact(g2, p2s as nat);
                    let rn2 = (k as nat / g2) as int;
                    let rd2 = (p2s as nat / g2) as int;
                    assert(rn2 <= k as int && rd2 <= p2s as int) by (nonlinear_arith)
                        requires
                            k as int == g2 as int * rn2,
                            p2s as int == g2 as int * rd2,
                            g2 >= 1,
                            rn2 >= 0,
                            rd2 >= 0;
                    lemma2_to64_rest();
                    lemma_pow2_strictly_increases(s as nat, 62);
                    assert(pow2(62) == 0x4000000000000000);
                }
                let r = make_canonical(neg, k as u128, p2s);
                let q = match r {
                    Some(q) => q,
                    None => {
                        proof {
                            assert(false);
                        }
                        Q::zero()
                    },
                };
                proof {
                    let g2 = gcd(k as nat, p2s as nat);
                    let rn2 = (k as nat / g2) as int;
                    let rd2 = (p2s as nat / g2) as int;
                    lemma_signed_value(
                        q.num_s(), q.den_s(), g2 as int, rn2, rd2, neg, k as int, p2s as int);
                    // value clause of the round arm:
                    // q.num * 2^s == (+-k) * q.den
                    assert(q.num_s() * pow2(s as nat) == (if en < 0 { -(k as int) } else { k as int }) * q.den_s());
                    // the middle-case guard: |en| <= MAX * ed
                    lemma_pow2_pos(s as nat);
                    assert(un as int <= max_mag() * (ud as int)) by (nonlinear_arith)
                        requires
                            (un as int) * pow2(s as nat) <= max_mag() * (ud as int),
                            pow2(s as nat) >= 1,
                            un >= 0;
                    // the exists witness
                    assert(signed_mag_round(k as int, s as nat, en, ud as int, dir));
                    assert(is_scale(s as nat, abs_i(en), ud as int));
                }
                q
            } else {
                // |en / ed| > MAX: saturate (documented; R2/R3 do not apply)
                proof {
                    lemma_gcd_x_one(max_mag() as nat);
                    lemma_gcd_x_one(1);
                }
                let r = make_canonical(neg, MAX_MAG as u128, 1);
                let q = match r {
                    Some(q) => q,
                    None => {
                        proof {
                            assert(false);
                        }
                        Q::zero()
                    },
                };
                proof {
                    assert(abs_i(en) > max_mag() * (ud as int));
                }
                q
            }
        },
    }
}

// ---------------------------------------------------------------------------
// Uniqueness: round_char pins the result (the determinism theorems' engine)
// ---------------------------------------------------------------------------

/// The chosen scale is unique.
pub proof fn lemma_scale_unique(s1: nat, s2: nat, un: int, ud: int)
    requires
        un >= 0,
        ud > 0,
        is_scale(s1, un, ud),
        is_scale(s2, un, ud),
    ensures
        s1 == s2,
{
    if s1 < s2 {
        lemma_scale_order_contra(s1, s2, un, ud);
    } else if s2 < s1 {
        lemma_scale_order_contra(s2, s1, un, ud);
    }
}

proof fn lemma_scale_order_contra(s1: nat, s2: nat, un: int, ud: int)
    requires
        un >= 0,
        ud > 0,
        s1 < s2,
        is_scale(s1, un, ud),
        is_scale(s2, un, ud),
    ensures
        false,
{
    // s1 < 61, so un * 2^(s1+1) > MAX * ud; but s1+1 <= s2 and the s2
    // constraint bounds un * 2^(s2) <= MAX * ud.
    if s1 + 1 < s2 {
        lemma_pow2_strictly_increases((s1 + 1) as nat, s2);
    }
    assert(un * pow2((s1 + 1) as nat) <= un * pow2(s2)) by (nonlinear_arith)
        requires
            un >= 0,
            pow2((s1 + 1) as nat) <= pow2(s2);
}

/// The directed-rounded numerator is unique at a given scale.
pub proof fn lemma_mag_round_unique(k1: int, k2: int, s: nat, un: int, ud: int, mdir: Dir)
    requires
        un >= 0,
        ud > 0,
        is_mag_round(k1, s, un, ud, mdir),
        is_mag_round(k2, s, un, ud, mdir),
    ensures
        k1 == k2,
{
    let t = un * pow2(s);
    match mdir {
        Dir::Down => {
            assert(k1 == k2) by (nonlinear_arith)
                requires
                    k1 * ud <= t < (k1 + 1) * ud,
                    k2 * ud <= t < (k2 + 1) * ud,
                    ud > 0;
        },
        Dir::Up => {
            assert(k1 == k2) by (nonlinear_arith)
                requires
                    (k1 - 1) * ud < t <= k1 * ud,
                    (k2 - 1) * ud < t <= k2 * ud,
                    ud > 0;
        },
        Dir::Nearest => {
            // Both arms place 2*k*ud in the half-open window (2t - ud, 2t + ud],
            // which contains at most one multiple of 2*ud.
            lemma_nearest_window(k1, s, un, ud);
            lemma_nearest_window(k2, s, un, ud);
            assert(k1 == k2) by (nonlinear_arith)
                requires
                    2 * t - ud < 2 * (k1 * ud) <= 2 * t + ud,
                    2 * t - ud < 2 * (k2 * ud) <= 2 * t + ud,
                    ud > 0;
        },
    }
}

proof fn lemma_nearest_window(k: int, s: nat, un: int, ud: int)
    requires
        ud > 0,
        is_mag_round(k, s, un, ud, Dir::Nearest),
    ensures
        2 * (un * pow2(s)) - ud < 2 * (k * ud) <= 2 * (un * pow2(s)) + ud,
{
}

/// `round_char` pins the result: two canonical results characterized
/// against the same exact fraction and direction are identical. This is
/// the engine behind determinism theorems (e.g. commutativity of add/mul).
pub proof fn lemma_round_char_unique(q1: Q, q2: Q, en: int, ed: int, dir: Dir)
    requires
        ed > 0,
        q1.inv(),
        q2.inv(),
        round_char(q1, en, ed, dir),
        round_char(q2, en, ed, dir),
    ensures
        q1 == q2,
{
    if new_fits(en, ed) {
        assert(q1.num_s() * q2.den_s() == q2.num_s() * q1.den_s()) by (nonlinear_arith)
            requires
                q1.num_s() * ed == en * q1.den_s(),
                q2.num_s() * ed == en * q2.den_s(),
                ed > 0;
        lemma_canonical_unique(q1, q2);
    } else if abs_i(en) <= max_mag() * ed {
        let (s1, k1) = choose|s: nat, k: int|
            is_scale(s, abs_i(en), ed) && #[trigger] signed_mag_round(k, s, en, ed, dir)
                && q1.num_s() * pow2(s) == (if en < 0 { -k } else { k }) * q1.den_s();
        let (s2, k2) = choose|s: nat, k: int|
            is_scale(s, abs_i(en), ed) && #[trigger] signed_mag_round(k, s, en, ed, dir)
                && q2.num_s() * pow2(s) == (if en < 0 { -k } else { k }) * q2.den_s();
        lemma_scale_unique(s1, s2, abs_i(en), ed);
        lemma_mag_round_unique(k1, k2, s1, abs_i(en), ed, mag_dir(dir, en < 0));
        let sk = if en < 0 { -k1 } else { k1 };
        lemma_pow2_pos(s1);
        assert(q1.num_s() * q2.den_s() == q2.num_s() * q1.den_s()) by (nonlinear_arith)
            requires
                q1.num_s() * pow2(s1) == sk * q1.den_s(),
                q2.num_s() * pow2(s1) == sk * q2.den_s(),
                pow2(s1) > 0;
        lemma_canonical_unique(q1, q2);
    } else {
        assert(q1.num_s() * q2.den_s() == q2.num_s() * q1.den_s());
        lemma_canonical_unique(q1, q2);
    }
}

// ---------------------------------------------------------------------------
// Correctness: round_char implies the R1-R3 contract
// ---------------------------------------------------------------------------

/// Derive the human-facing contract (`rounds_to`) from the pipeline
/// characterization (`round_char`).
pub proof fn lemma_round_char_correct(q: Q, en: int, ed: int, dir: Dir)
    requires
        ed > 0,
        q.inv(),
        round_char(q, en, ed, dir),
    ensures
        rounds_to(q, en, ed, dir),
{
    let diff = q.num_s() * ed - en * q.den_s();
    if new_fits(en, ed) {
        assert(diff == 0);
        assert(abs_i(diff) == 0);
        assert(q.den_s() * ed >= 0) by (nonlinear_arith)
            requires q.den_s() > 0, ed > 0;
        assert(q.den_s() * abs_i(en) >= 0) by (nonlinear_arith)
            requires q.den_s() > 0, abs_i(en) >= 0;
        assert(abs_i(diff) * pow2(60) == 0) by (nonlinear_arith)
            requires abs_i(diff) == 0;
    } else if abs_i(en) <= max_mag() * ed {
        let (s, k) = choose|s: nat, k: int|
            is_scale(s, abs_i(en), ed) && #[trigger] signed_mag_round(k, s, en, ed, dir)
                && q.num_s() * pow2(s) == (if en < 0 { -k } else { k }) * q.den_s();
        let un = abs_i(en);
        let ud = ed;
        let t = un * pow2(s);
        let sk = if en < 0 { -k } else { k };
        let mdir = mag_dir(dir, en < 0);
        lemma_pow2_pos(s);

        // Grid error window on magnitudes, |k*ud - t| <= ud, any mode:
        match mdir {
            Dir::Down => {
                assert(-ud <= t - k * ud <= ud) by (nonlinear_arith)
                    requires
                        k * ud <= t,
                        t < (k + 1) * ud,
                        ud > 0;
            },
            Dir::Up => {
                assert(-ud <= t - k * ud <= ud) by (nonlinear_arith)
                    requires
                        (k - 1) * ud < t,
                        t <= k * ud,
                        ud > 0;
            },
            Dir::Nearest => {
                lemma_nearest_window(k, s, un, ud);
                assert(-ud <= t - k * ud <= ud) by (nonlinear_arith)
                    requires
                        2 * t - ud < 2 * (k * ud) <= 2 * t + ud,
                        ud > 0;
            },
        }
        assert(-ud <= t - k * ud <= ud);

        // diff * 2^s == q.den * (sk*ed - en*2^s), and the parenthesized term
        // is the (sign-pushed) grid error.
        assert(diff * pow2(s) == q.den_s() * (sk * ed - en * pow2(s))) by (nonlinear_arith)
            requires
                diff == q.num_s() * ed - en * q.den_s(),
                q.num_s() * pow2(s) == sk * q.den_s();
        // sign push: sk*ed - en*2^s == (k*ud - t) or -(k*ud - t)
        if en < 0 {
            assert(sk * ed - en * pow2(s) == -(k * ud - t)) by (nonlinear_arith)
                requires
                    sk == -k,
                    en == -un,
                    t == un * pow2(s),
                    ud == ed;
        } else {
            assert(sk * ed - en * pow2(s) == k * ud - t) by (nonlinear_arith)
                requires
                    sk == k,
                    en == un,
                    t == un * pow2(s),
                    ud == ed;
        }
        // Two-sided bound on diff * 2^s:
        assert(-(q.den_s() * ud) <= diff * pow2(s) <= q.den_s() * ud) by (nonlinear_arith)
            requires
                diff * pow2(s) == q.den_s() * (sk * ed - en * pow2(s)),
                (sk * ed - en * pow2(s) == k * ud - t) || (sk * ed - en * pow2(s) == -(k * ud - t)),
                -ud <= t - k * ud <= ud,
                q.den_s() > 0;

        // ---- R2 (directed) ----
        if dir == Dir::Down {
            if en < 0 {
                // magnitude ceil: t <= k*ud
                assert(diff <= 0) by (nonlinear_arith)
                    requires
                        diff * pow2(s) == q.den_s() * (sk * ed - en * pow2(s)),
                        sk * ed - en * pow2(s) == -(k * ud - t),
                        t <= k * ud,
                        q.den_s() > 0,
                        pow2(s) > 0;
            } else {
                // magnitude floor: k*ud <= t
                assert(diff <= 0) by (nonlinear_arith)
                    requires
                        diff * pow2(s) == q.den_s() * (sk * ed - en * pow2(s)),
                        sk * ed - en * pow2(s) == k * ud - t,
                        k * ud <= t,
                        q.den_s() > 0,
                        pow2(s) > 0;
            }
        }
        if dir == Dir::Up {
            if en < 0 {
                assert(diff >= 0) by (nonlinear_arith)
                    requires
                        diff * pow2(s) == q.den_s() * (sk * ed - en * pow2(s)),
                        sk * ed - en * pow2(s) == -(k * ud - t),
                        k * ud <= t,
                        q.den_s() > 0,
                        pow2(s) > 0;
            } else {
                assert(diff >= 0) by (nonlinear_arith)
                    requires
                        diff * pow2(s) == q.den_s() * (sk * ed - en * pow2(s)),
                        sk * ed - en * pow2(s) == k * ud - t,
                        t <= k * ud,
                        q.den_s() > 0,
                        pow2(s) > 0;
            }
        }

        // ---- R3 (error bound, B = 60) ----
        lemma2_to64();
        lemma2_to64_rest();
        lemma_pow2_adds(60, 1);
        assert(pow2(61) == 2 * pow2(60));
        if un <= ud {
            // Small values always get the finest grid: s == 61.
            if s < 61 {
                lemma_pow2_strictly_increases((s + 1) as nat, 62);
                assert(un * pow2((s + 1) as nat) <= max_mag() * ud) by (nonlinear_arith)
                    requires
                        un <= ud,
                        un >= 0,
                        ud > 0,
                        pow2((s + 1) as nat) < pow2(62),
                        pow2(62) == 0x4000000000000000,
                        max_mag() == 0x3FFF_FFFF_FFFF_FFFF;
                assert(false);
            }
            assert(abs_i(diff) * pow2(60) <= q.den_s() * ed) by (nonlinear_arith)
                requires
                    -(q.den_s() * ud) <= diff * pow2(s) <= q.den_s() * ud,
                    (diff >= 0 ==> abs_i(diff) == diff) && (diff < 0 ==> abs_i(diff) == -diff),
                    pow2(s) == 2 * pow2(60),
                    ud == ed,
                    q.den_s() > 0,
                    ud > 0,
                    pow2(60) > 0;
        } else {
            // un > ud: relative bound against |en| == un.
            if s == 61 {
                assert(abs_i(diff) * pow2(60) <= q.den_s() * un) by (nonlinear_arith)
                    requires
                        -(q.den_s() * ud) <= diff * pow2(s) <= q.den_s() * ud,
                        (diff >= 0 ==> abs_i(diff) == diff) && (diff < 0 ==> abs_i(diff) == -diff),
                        pow2(s) == 2 * pow2(60),
                        un > ud,
                        ud > 0,
                        q.den_s() > 0,
                        pow2(60) > 0;
            } else {
                // maximality of s: un * 2^(s+1) > MAX * ud >= 2^61 * ud,
                // so ud * 2^60 <= un * 2^s.
                lemma_pow2_adds(s, 1);
                assert(pow2((s + 1) as nat) == pow2(s) * 2);
                assert(ud * pow2(60) <= un * pow2(s)) by (nonlinear_arith)
                    requires
                        un * (pow2(s) * 2) > max_mag() * ud,
                        max_mag() >= 2 * pow2(60),
                        ud > 0,
                        un >= 0,
                        pow2(s) > 0,
                        pow2(60) > 0;
                assert(abs_i(diff) * pow2(60) <= q.den_s() * un) by (nonlinear_arith)
                    requires
                        -(q.den_s() * ud) <= diff * pow2(s) <= q.den_s() * ud,
                        (diff >= 0 ==> abs_i(diff) == diff) && (diff < 0 ==> abs_i(diff) == -diff),
                        ud * pow2(60) <= un * pow2(s),
                        ud > 0,
                        q.den_s() > 0,
                        pow2(s) > 0,
                        pow2(60) > 0;
            }
        }
    } else {
        // saturation: R1's hypothesis is false and R2/R3's guard is false.
    }
}

// ---------------------------------------------------------------------------
// R4: monotonicity on a shared grid
// ---------------------------------------------------------------------------

/// Directed rounding is monotone across two magnitudes on the same grid
/// (same scale `s`, same mode): if `un1/ud1 <= un2/ud2` then `k1 <= k2`.
pub proof fn lemma_mag_round_monotone(
    k1: int, k2: int, s: nat, un1: int, ud1: int, un2: int, ud2: int, mdir: Dir)
    requires
        un1 >= 0,
        un2 >= 0,
        ud1 > 0,
        ud2 > 0,
        un1 * ud2 <= un2 * ud1,
        is_mag_round(k1, s, un1, ud1, mdir),
        is_mag_round(k2, s, un2, ud2, mdir),
    ensures
        k1 <= k2,
{
    let t1 = un1 * pow2(s);
    let t2 = un2 * pow2(s);
    lemma_pow2_pos(s);
    // Cross-scaled order: t1 * ud2 <= t2 * ud1.
    assert(t1 * ud2 <= t2 * ud1) by (nonlinear_arith)
        requires
            t1 == un1 * pow2(s),
            t2 == un2 * pow2(s),
            un1 * ud2 <= un2 * ud1,
            pow2(s) > 0;
    match mdir {
        Dir::Down => {
            assert(k1 <= k2) by (nonlinear_arith)
                requires
                    k1 * ud1 <= t1 < (k1 + 1) * ud1,
                    k2 * ud2 <= t2 < (k2 + 1) * ud2,
                    t1 * ud2 <= t2 * ud1,
                    ud1 > 0,
                    ud2 > 0;
        },
        Dir::Up => {
            assert(k1 <= k2) by (nonlinear_arith)
                requires
                    (k1 - 1) * ud1 < t1 <= k1 * ud1,
                    (k2 - 1) * ud2 < t2 <= k2 * ud2,
                    t1 * ud2 <= t2 * ud1,
                    ud1 > 0,
                    ud2 > 0;
        },
        Dir::Nearest => {
            lemma_nearest_window(k1, s, un1, ud1);
            lemma_nearest_window(k2, s, un2, ud2);
            assert(k1 <= k2) by (nonlinear_arith)
                requires
                    2 * t1 - ud1 < 2 * (k1 * ud1) <= 2 * t1 + ud1,
                    2 * t2 - ud2 < 2 * (k2 * ud2) <= 2 * t2 + ud2,
                    t1 * ud2 <= t2 * ud1,
                    ud1 > 0,
                    ud2 > 0;
        },
    }
}

} // verus!
