//! The rounding contract R1–R4 (obligation V4), and the single canonicalising
//! entry point every arithmetic operation funnels through.
//!
//! # The algorithm
//!
//! [`round_frac_exec`] takes an *exact* fraction `n / d` computed in `i128` and
//! produces the `Q` that the operation returns:
//!
//! 1. `n == 0` → `0/1`.
//! 2. `|n/d| > MAX_MAG` → **saturate** to `±MAX_MAG/1`. No `Q` is within the R3
//!    bound of such a value, so this case is outside the contract; the
//!    `checked_*` operations surface it as `None` instead.
//! 3. Reduce by `gcd(|n|, d)`. If the reduced pair fits the budget, return it
//!    **exactly** — this is R1, and it is why small investigations pay zero
//!    rounding.
//! 4. Otherwise **dyadic snap**: pick a shift `s`, round `n·2^s / d` to an
//!    integer in the requested direction, and return that over `2^s`
//!    (re-reduced).
//!
//! # Choosing the shift
//!
//! With `k = bitlen(floor(|x|))` (so `2^(k-1) <= |x| < 2^k` for `|x| >= 1`, and
//! `k = 0` for `|x| < 1`), the shift is `s = 61 - k`, clamped to `0`.
//!
//! * The grid step is `2^-s`, so the error is at most `2^-s = 2^(k-61)`.
//! * The bound R3 demands is `2^-60 · max(1, |x|) >= 2^-60 · 2^(k-1) = 2^(k-61)`.
//!
//! The two meet exactly: `B = 60` is achieved, which is the specification's
//! acceptance bar. The numerator stays inside the budget because
//! `|x| · 2^s < 2^k · 2^(61-k) = 2^61`, and the denominator is `2^s <= 2^61`.
//!
//! # No overflow (V2)
//!
//! `n·2^s` is *never* materialised — it would overflow `i128`. [`shift_div`]
//! instead walks `s <= 61` doubling steps carrying only a quotient (`< 2^62`)
//! and a remainder (`< d <= 2^124`), so the widest live value is `2·d < 2^125`.

use verus_builtin_macros::verus;

#[allow(unused_imports)]
use verus_builtin::*;
#[allow(unused_imports)]
use vstd::prelude::*;

#[allow(unused_imports)]
use crate::gcd::*;
#[allow(unused_imports)]
use crate::model::*;
use crate::types::{Dir, MAX_MAG, Q};

verus! {

// ---------------------------------------------------------------------------
// The rounding specification (the mirror the executable code is proven equal to)
// ---------------------------------------------------------------------------

/// The dyadic shift chosen for the value `n / d`.
pub open spec fn snap_shift(n: int, d: int) -> nat {
    let k = bitlen(abs_int(n) / d);
    if k >= 61 {
        0nat
    } else {
        (61 - k) as nat
    }
}

/// The integer `n·2^s / d` rounded in direction `dir`.
///
/// Verus `int` division is Euclidean, which for `d > 0` is floor division, so
/// `a / d` is `floor(a/d)` and `-((-a) / d)` is `ceil(a/d)` — including for
/// negative `a`. `Nearest` breaks ties to an even numerator, which is
/// sign-symmetric (rounding `-x` gives the negation of rounding `x`).
pub open spec fn grid_num(n: int, d: int, s: nat, dir: Dir) -> int {
    let a = n * pow2(s);
    match dir {
        Dir::Down => a / d,
        Dir::Up => -((-a) / d),
        Dir::Nearest => {
            let q = a / d;
            let r = a % d;
            if 2 * r > d {
                q + 1
            } else if 2 * r < d {
                q
            } else if q % 2 == 0 {
                q
            } else {
                q + 1
            }
        },
    }
}

/// The numerator of the reduction of `n / d`.
pub open spec fn red_num(n: int, d: int) -> int {
    n / gcd_int(n, d)
}

/// The denominator of the reduction of `n / d`.
pub open spec fn red_den(n: int, d: int) -> int {
    d / gcd_int(n, d)
}

/// Whether the *reduced* form of `n / d` satisfies I2 — i.e. whether the
/// operation is on the exact path (R1).
pub open spec fn exact_path(n: int, d: int) -> bool {
    n == 0 || fits_budget(red_num(n, d), red_den(n, d))
}

/// The complete rounding function, in ghost form.
///
/// Every arithmetic operation `ensures` that its result is *equal to* this
/// applied to the exact numerator and denominator. Pinning the result down as a
/// function (rather than only by its properties) is what makes commutativity
/// and cross-run determinism provable at all: `add(a, b)` and `add(b, a)` feed
/// provably equal `int`s into the same function.
pub open spec fn round_frac(n: int, d: int, dir: Dir) -> Q {
    if n == 0 {
        Q { num: 0, den: 1 }
    } else if !magnitude_fits(n, d) {
        if n > 0 {
            Q { num: MAX_MAG, den: 1 }
        } else {
            Q { num: (-(MAX_MAG as int)) as i64, den: 1 }
        }
    } else {
        let rn = red_num(n, d);
        let rd = red_den(n, d);
        if fits_budget(rn, rd) {
            Q { num: rn as i64, den: rd as i64 }
        } else {
            let s = snap_shift(rn, rd);
            let sn = grid_num(rn, rd, s, dir);
            let sd = pow2(s);
            let g2 = gcd_int(sn, sd);
            Q { num: (sn / g2) as i64, den: (sd / g2) as i64 }
        }
    }
}

/// Whether [`round_frac`] saturated, i.e. the exact value was too large in
/// magnitude to be represented at all. The `checked_*` operations return `None`
/// exactly here.
pub open spec fn saturated(n: int, d: int) -> bool {
    n != 0 && !magnitude_fits(n, d)
}

// ---------------------------------------------------------------------------
// R1 — identity on representables
// ---------------------------------------------------------------------------

/// **R1.** If the exact reduced result fits the budget, it is returned exactly.
///
/// Consequence (the exactness theorem): a computation all of whose exact
/// intermediate values fit the budget is end-to-end exact. It is stated for
/// whole computations as `theorem_exact_path_is_exact` in [`crate::laws`].
pub proof fn lemma_r1_identity(n: int, d: int, dir: Dir)
    requires
        d > 0,
        exact_path(n, d),
    ensures
        q_is(round_frac(n, d, dir), n, d),
        round_frac(n, d, dir).wf(),
{
    crate::model::lemma_max_mag_pow2();
    if n == 0 {
        assert(round_frac(n, d, dir) == Q { num: 0, den: 1 });
        lemma_gcd_one();
    } else {
        let g = gcd_int(n, d);
        lemma_gcd_pos(abs_int(n) as nat, d as nat);
        lemma_gcd_divides(abs_int(n) as nat, d as nat);
        lemma_reduce_exact(n, d);
        lemma_reduce_abs(n, d);
        let rn = red_num(n, d);
        let rd = red_den(n, d);
        assert(n == rn * g && d == rd * g);
        // magnitude_fits unfolded: |n| == |rn|·g <= M·g <= M·(rd·g) == M·d.
        // Stated as `magnitude_fits(n, d)` the block cannot unfold the
        // definition, so spell the inequality out.
        assert(abs_int(n) <= max_mag() * d) by (nonlinear_arith)
            requires
                abs_int(n) == abs_int(rn) * g,
                abs_int(rn) <= max_mag(),
                max_mag() > 0,
                rd >= 1,
                g >= 1,
                d == rd * g,
        ;
        let r = round_frac(n, d, dir);
        assert(r == Q { num: rn as i64, den: rd as i64 });
        // I1's zero clause: `n != 0` and `n == rn·g` force `rn != 0`, so the
        // clause is vacuous here.
        assert(rn != 0) by (nonlinear_arith)
            requires
                n != 0,
                n == rn * g,
        ;
        assert(r.n() * d == n * r.d()) by (nonlinear_arith)
            requires
                n == rn * g,
                d == rd * g,
                r.n() == rn,
                r.d() == rd,
        ;
        lemma_gcd_reduce_coprime(abs_int(n) as nat, d as nat);
    }
}

/// The reduction really is exact: `n == red_num · g` and `d == red_den · g`.
pub proof fn lemma_reduce_exact(n: int, d: int)
    requires
        d > 0,
    ensures
        n == red_num(n, d) * gcd_int(n, d),
        d == red_den(n, d) * gcd_int(n, d),
        red_den(n, d) > 0,
        gcd_int(n, d) > 0,
{
    let g = gcd_int(n, d);
    lemma_gcd_pos(abs_int(n) as nat, d as nat);
    lemma_gcd_divides(abs_int(n) as nat, d as nat);
    let kd = choose|k: int| d == #[trigger] (g * k);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(d, g, kd, 0);
    assert(kd > 0) by (nonlinear_arith)
        requires
            d > 0,
            g > 0,
            d == g * kd,
    ;
    let ka = choose|k: int| abs_int(n) == #[trigger] (g * k);
    if n >= 0 {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(n, g, ka, 0);
    } else {
        assert(n == g * (-ka)) by (nonlinear_arith)
            requires
                abs_int(n) == g * ka,
                n < 0,
                abs_int(n) == -n,
        ;
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(n, g, -ka, 0);
    }
}

/// Reduction never makes either component larger.
///
/// `lemma_snap_in_budget` bounds the *snapped* pair, but `round_frac` returns
/// that pair divided through by its gcd; this is what carries the I2 bound the
/// last step.
pub proof fn lemma_reduce_shrinks(n: int, d: int)
    requires
        d > 0,
    ensures
        abs_int(red_num(n, d)) <= abs_int(n),
        0 < red_den(n, d) <= d,
{
    let g = gcd_int(n, d);
    lemma_reduce_exact(n, d);
    lemma_reduce_abs(n, d);
    assert(abs_int(red_num(n, d)) <= abs_int(n)) by (nonlinear_arith)
        requires
            g >= 1,
            abs_int(n) == abs_int(red_num(n, d)) * g,
            abs_int(red_num(n, d)) >= 0,
    ;
    assert(red_den(n, d) <= d) by (nonlinear_arith)
        requires
            g >= 1,
            d == red_den(n, d) * g,
            red_den(n, d) > 0,
    ;
}

/// The magnitude of the reduced numerator is the reduction of the magnitude:
/// `|n| / g == |n / g|`.
///
/// This is the bridge between [`crate::gcd::lemma_gcd_reduce_coprime`], which is
/// stated on `nat` magnitudes, and `gcd_int(red_num, red_den) == 1`, which is
/// what invariant I1 actually asks for.
pub proof fn lemma_reduce_abs(n: int, d: int)
    requires
        d > 0,
    ensures
        abs_int(n) == abs_int(red_num(n, d)) * gcd_int(n, d),
        abs_int(n) / gcd_int(n, d) == abs_int(red_num(n, d)),
{
    let g = gcd_int(n, d);
    let rn = red_num(n, d);
    lemma_reduce_exact(n, d);
    assert(abs_int(n) == abs_int(rn) * g) by (nonlinear_arith)
        requires
            n == rn * g,
            g > 0,
            abs_int(n) == (if n >= 0 { n } else { -n }),
            abs_int(rn) == (if rn >= 0 { rn } else { -rn }),
    ;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(abs_int(n), g, abs_int(rn), 0);
}

/// `round_frac` always produces a well-formed `Q` — the V1 obligation stated at
/// the specification level, so proof code can use it without going through the
/// executable function.
///
/// Four cases, matching the four branches: zero, saturation, the exact path, and
/// the dyadic snap. Canonicality comes from `lemma_gcd_reduce_coprime` in the
/// two reducing branches; the bounds come from `fits_budget` and
/// `lemma_snap_in_budget` respectively.
pub proof fn lemma_round_frac_wf(n: int, d: int, dir: Dir)
    requires
        d > 0,
    ensures
        round_frac(n, d, dir).wf(),
{
    lemma_gcd_one();
    crate::model::lemma_max_mag_pow2();
    if n == 0 {
    } else if !magnitude_fits(n, d) {
    } else {
        lemma_reduce_exact(n, d);
        let rn = red_num(n, d);
        let rd = red_den(n, d);
        lemma_gcd_reduce_coprime(abs_int(n) as nat, d as nat);
        // `lemma_gcd_reduce_coprime` speaks about `|n| / g`; this identifies
        // that with `|red_num|`, which is what `gcd_int(rn, rd)` unfolds to.
        lemma_reduce_abs(n, d);
        lemma_reduce_magnitude_fits(n, d);
        if fits_budget(rn, rd) {
        } else {
            let s = snap_shift(rn, rd);
            let sn = grid_num(rn, rd, s, dir);
            let sd = pow2(s);
            lemma_pow2_pos(s);
            lemma_grid_error_step(rn, rd, s, dir);
            lemma_snap_magnitude(rn, rd, s, dir);
            // Coprimality of the reduced pair is what makes the numerator
            // bound true at the clamped shift; `lemma_gcd_reduce_coprime`
            // above established it.
            assert(gcd_int(rn, rd) == 1);
            assert(rn != 0) by (nonlinear_arith)
                requires
                    n != 0,
                    n == rn * gcd_int(n, d),
            ;
            lemma_snap_in_budget(rn, rd, s, sn, crate::model::bitlen(abs_int(rn) / rd));
            lemma_reduce_exact(sn, sd);
            lemma_gcd_reduce_coprime(abs_int(sn) as nat, sd as nat);
            lemma_reduce_abs(sn, sd);
            // I2 is bounded on `sn` and `sd`; the returned pair is those
            // divided by their gcd, which can only be smaller.
            lemma_reduce_shrinks(sn, sd);
            // Spell out the five clauses of `wf` against the returned pair, so
            // a future failure names the clause instead of the conjunction.
            let g2 = gcd_int(sn, sd);
            let on = red_num(sn, sd);
            let od = red_den(sn, sd);
            // I1's zero clause, guarded on the *reduced* numerator — which is
            // what `wf` looks at. `sn == on·g2`, so a zero `on` means a zero
            // `sn`, which makes the gcd the whole denominator.
            if on == 0 {
                // Even `0 · g2` is an uninterpreted product out here.
                assert(sn == 0) by (nonlinear_arith)
                    requires
                        sn == on * g2,
                        on == 0,
                ;
                crate::gcd::lemma_gcd_zero(sd as nat);
                assert(g2 == sd);
                vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(sd, sd, 1, 0);
                assert(od == 1);
            }
            assert(round_frac(n, d, dir) == Q { num: on as i64, den: od as i64 });
            assert(od > 0);
            assert(abs_int(on) <= max_mag());
            assert(od <= max_mag());
            assert(on == 0 ==> od == 1);
            assert(gcd_int(on, od) == 1);
        }
    }
}

/// In the snapping branch the result's fields *are* the reduced snapped pair.
///
/// `round_frac` writes them through `as i64`, so this is where the round-trip
/// is discharged — which is what `lemma_snap_in_budget` is for.
pub proof fn lemma_snap_result_fields(n: int, d: int, dir: Dir)
    requires
        d > 0,
        n != 0,
        magnitude_fits(n, d),
        !exact_path(n, d),
    ensures
        ({
            let rn = red_num(n, d);
            let rd = red_den(n, d);
            let s = snap_shift(rn, rd);
            let sn = grid_num(rn, rd, s, dir);
            let sd = pow2(s);
            let r = round_frac(n, d, dir);
            &&& r.n() == red_num(sn, sd)
            &&& r.d() == red_den(sn, sd)
            &&& sn == r.n() * gcd_int(sn, sd)
            &&& sd == r.d() * gcd_int(sn, sd)
            &&& gcd_int(sn, sd) > 0
            &&& r.d() > 0
        }),
{
    lemma_round_frac_wf(n, d, dir);
    crate::model::lemma_max_mag_pow2();
    lemma_reduce_exact(n, d);
    lemma_gcd_reduce_coprime(abs_int(n) as nat, d as nat);
    lemma_reduce_abs(n, d);
    lemma_reduce_magnitude_fits(n, d);
    let rn = red_num(n, d);
    let rd = red_den(n, d);
    let s = snap_shift(rn, rd);
    let sn = grid_num(rn, rd, s, dir);
    let sd = pow2(s);
    lemma_pow2_pos(s);
    lemma_grid_error_step(rn, rd, s, dir);
    lemma_snap_magnitude(rn, rd, s, dir);
    assert(rn != 0) by (nonlinear_arith)
        requires
            n != 0,
            n == rn * gcd_int(n, d),
    ;
    lemma_snap_in_budget(rn, rd, s, sn, crate::model::bitlen(abs_int(rn) / rd));
    lemma_reduce_exact(sn, sd);
    lemma_gcd_reduce_coprime(abs_int(sn) as nat, sd as nat);
    lemma_reduce_abs(sn, sd);
    lemma_reduce_shrinks(sn, sd);
    if sn == 0 {
        crate::gcd::lemma_gcd_zero(sd as nat);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(sd, sd, 1, 0);
    }
}

/// Re-reducing the snapped pair by its gcd preserves the grid error bound.
///
/// The bound comes out of `lemma_grid_error_step` and `lemma_shift_covers_bound`
/// stated against `sn / 2^s`; `round_frac` returns that pair divided through by
/// its gcd, and the inequality survives because both sides carry the factor.
pub proof fn lemma_error_after_reduce(rn: int, rd: int, sn: int, sd: int, g2: int, r: Q)
    requires
        g2 > 0,
        r.d() > 0,
        sn == r.n() * g2,
        sd == r.d() * g2,
        abs_int(sn * rd - rn * sd) * pow2(precision_b()) <= sd * max_int(rd, abs_int(rn)),
    ensures
        abs_int(r.n() * rd - rn * r.d()) * pow2(precision_b()) <= r.d() * max_int(rd, abs_int(rn)),
{
    let e = abs_int(r.n() * rd - rn * r.d());
    let m = max_int(rd, abs_int(rn));
    assert(sn * rd - rn * sd == (r.n() * rd - rn * r.d()) * g2) by (nonlinear_arith)
        requires
            sn == r.n() * g2,
            sd == r.d() * g2,
    ;
    assert(abs_int((r.n() * rd - rn * r.d()) * g2) == e * g2) by (nonlinear_arith)
        requires
            g2 > 0,
            e == abs_int(r.n() * rd - rn * r.d()),
    ;
    assert((e * g2) * pow2(precision_b()) == (e * pow2(precision_b())) * g2) by (nonlinear_arith);
    assert(sd * m == (r.d() * m) * g2) by (nonlinear_arith)
        requires
            sd == r.d() * g2,
    ;
    assert(e * pow2(precision_b()) <= r.d() * m) by (nonlinear_arith)
        requires
            g2 > 0,
            (e * pow2(precision_b())) * g2 <= (r.d() * m) * g2,
    ;
}

/// `gcd(x, 1) == 1` for every `x` — needed for the zero and saturating branches,
/// whose denominators are `1`.
pub proof fn lemma_gcd_one()
    ensures
        forall|x: int| #[trigger] gcd_int(x, 1) == 1,
{
    assert forall|x: int| #[trigger] gcd_int(x, 1) == 1 by {
        crate::model::lemma_gcd_unit(x);
    }
}

/// The snapped numerator is within one of the exact scaled value, which is the
/// form `lemma_snap_in_budget` consumes.
///
/// From `|sn·rd - rn·2^s| <= rd` (one grid step) and
/// `|rn|·2^s == q·rd + r` with `0 <= r < rd`, we get
/// `|sn|·rd <= q·rd + r + rd < (q + 2)·rd`, hence `|sn| <= q + 1`.
pub proof fn lemma_snap_magnitude(rn: int, rd: int, s: nat, dir: Dir)
    requires
        rd > 0,
    ensures
        abs_int(grid_num(rn, rd, s, dir)) <= abs_int(rn) * pow2(s) / rd + 1,
{
    lemma_pow2_pos(s);
    lemma_grid_error_step(rn, rd, s, dir);
    let sn = grid_num(rn, rd, s, dir);
    let m = abs_int(rn) * pow2(s);
    let q = m / rd;
    let r = m % rd;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(m, rd);
    assert(0 <= r < rd);
    assert(m == rd * q + r);
    crate::model::lemma_abs_mul_pos(sn, rd);
    crate::model::lemma_abs_mul_pos(rn, pow2(s));
    assert(abs_int(rn * pow2(s)) == m);
    // |sn·rd| <= |rn·2^s| + |sn·rd - rn·2^s| <= m + rd.
    assert(abs_int(sn) * rd <= m + rd) by (nonlinear_arith)
        requires
            abs_int(sn * rd - rn * pow2(s)) <= rd,
            abs_int(sn * rd) == abs_int(sn) * rd,
            abs_int(rn * pow2(s)) == m,
    ;
    assert(abs_int(sn) * rd < (q + 2) * rd) by (nonlinear_arith)
        requires
            rd > 0,
            abs_int(sn) * rd <= m + rd,
            m == rd * q + r,
            r < rd,
    ;
    assert(abs_int(sn) < q + 2) by (nonlinear_arith)
        requires
            rd > 0,
            abs_int(sn) * rd < (q + 2) * rd,
    ;
}

// ---------------------------------------------------------------------------
// R2 — directedness
// ---------------------------------------------------------------------------

/// **R2.** `Down` never exceeds the exact value; `Up` is never below it.
pub proof fn lemma_r2_directed(n: int, d: int)
    requires
        d > 0,
        !saturated(n, d),
    ensures
        q_le_frac(round_frac(n, d, Dir::Down), n, d),
        q_ge_frac(round_frac(n, d, Dir::Up), n, d),
{
    if exact_path(n, d) {
        lemma_r1_identity(n, d, Dir::Down);
        lemma_r1_identity(n, d, Dir::Up);
    } else {
        lemma_reduce_exact(n, d);
        let rn = red_num(n, d);
        let rd = red_den(n, d);
        let g = gcd_int(n, d);
        let s = snap_shift(rn, rd);
        lemma_pow2_pos(s);
        let sd = pow2(s);
        // floor: (rn * 2^s / rd) * rd <= rn * 2^s  <=  ceil(...) * rd
        let a = rn * sd;
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(a, rd);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(-a, rd);
        assert((a / rd) * rd == rd * (a / rd)) by (nonlinear_arith);
        assert(((-a) / rd) * rd == rd * ((-a) / rd)) by (nonlinear_arith);
        assert((rn * sd) / rd * rd <= rn * sd);
        assert(rn * sd <= -(((-(rn * sd)) / rd) * rd));
        // `grid_num(.., Up) == -((-a) / rd)`, so its product with `rd` is the
        // negation of the product above — a nonlinear step.
        assert((-(((-a) / rd))) * rd == -(((-a) / rd) * rd)) by (nonlinear_arith);
        lemma_grid_reduce_preserves_order(rn, rd, s, Dir::Down);
        lemma_grid_reduce_preserves_order(rn, rd, s, Dir::Up);
        // Carry the inequality from the snapped pair to the reduced one: both
        // sides pick up the same positive factor `g2`, which then cancels.
        lemma_snap_result_fields(n, d, Dir::Down);
        lemma_snap_result_fields(n, d, Dir::Up);
        lemma_order_after_reduce(rn, rd, s, Dir::Down);
        lemma_order_after_reduce(rn, rd, s, Dir::Up);
        lemma_scale_frac_order(n, d, g, rn, rd, round_frac(n, d, Dir::Down));
        lemma_scale_frac_order(n, d, g, rn, rd, round_frac(n, d, Dir::Up));
    }
}

/// Reducing `grid_num/2^s` by its gcd does not change the value, so it does not
/// change the direction of the inequality against `rn/rd`.
pub proof fn lemma_grid_reduce_preserves_order(rn: int, rd: int, s: nat, dir: Dir)
    requires
        rd > 0,
    ensures
        ({
            let sn = grid_num(rn, rd, s, dir);
            let sd = pow2(s);
            let g2 = gcd_int(sn, sd);
            &&& (sn / g2) * sd == sn * (sd / g2)
            &&& sd / g2 > 0
        }),
{
    let sn = grid_num(rn, rd, s, dir);
    let sd = pow2(s);
    lemma_pow2_pos(s);
    lemma_reduce_exact(sn, sd);
    let g2 = gcd_int(sn, sd);
    assert(sn == (sn / g2) * g2 && sd == (sd / g2) * g2);
    assert((sn / g2) * sd == sn * (sd / g2)) by (nonlinear_arith)
        requires
            sn == (sn / g2) * g2,
            sd == (sd / g2) * g2,
    ;
}

/// The reduced snapped pair sits on the same side of `rn/rd` as the snapped
/// pair does.
///
/// `Down` gives `sn·rd <= rn·2^s` and `Up` gives `sn·rd >= rn·2^s`; dividing
/// both members through by `g2 == gcd(sn, 2^s)` multiplies each side of the
/// inequality by the same positive factor, so it survives.
pub proof fn lemma_order_after_reduce(rn: int, rd: int, s: nat, dir: Dir)
    requires
        rd > 0,
    ensures
        ({
            let sn = grid_num(rn, rd, s, dir);
            let sd = pow2(s);
            let g2 = gcd_int(sn, sd);
            &&& (sn * rd <= rn * sd) ==> ((sn / g2) * rd <= rn * (sd / g2))
            &&& (sn * rd >= rn * sd) ==> ((sn / g2) * rd >= rn * (sd / g2))
        }),
{
    let sn = grid_num(rn, rd, s, dir);
    let sd = pow2(s);
    lemma_pow2_pos(s);
    lemma_reduce_exact(sn, sd);
    let g2 = gcd_int(sn, sd);
    let rsn = sn / g2;
    let rsd = sd / g2;
    assert(sn * rd == (rsn * rd) * g2) by (nonlinear_arith)
        requires
            sn == rsn * g2,
    ;
    assert(rn * sd == (rn * rsd) * g2) by (nonlinear_arith)
        requires
            sd == rsd * g2,
    ;
    assert(forall|x: int, y: int| #[trigger] (x * g2) <= #[trigger] (y * g2) <==> x <= y)
        by (nonlinear_arith)
        requires
            g2 > 0,
    ;
}

/// If `r` compares one way against `rn/rd`, it compares the same way against
/// `n/d == (rn·g)/(rd·g)`.
pub proof fn lemma_scale_frac_order(n: int, d: int, g: int, rn: int, rd: int, r: Q)
    requires
        g > 0,
        rd > 0,
        n == rn * g,
        d == rd * g,
    ensures
        (r.n() * rd <= rn * r.d()) == (r.n() * d <= n * r.d()),
        (r.n() * rd >= rn * r.d()) == (r.n() * d >= n * r.d()),
        (r.n() * rd == rn * r.d()) == (r.n() * d == n * r.d()),
{
    assert(r.n() * d == (r.n() * rd) * g) by (nonlinear_arith)
        requires
            d == rd * g,
    ;
    assert(n * r.d() == (rn * r.d()) * g) by (nonlinear_arith)
        requires
            n == rn * g,
    ;
    assert(forall|x: int, y: int| #[trigger] (x * g) <= #[trigger] (y * g) <==> x <= y)
        by (nonlinear_arith)
        requires
            g > 0,
    ;
}

// ---------------------------------------------------------------------------
// R3 — the error bound
// ---------------------------------------------------------------------------

/// **R3.** `|result - exact| <= 2^-60 · max(1, |exact|)`, for every direction.
///
/// The proof is the shift analysis from the module header, carried out
/// division-free. The three cases are `k = 0` (`|x| < 1`, `s = 61`),
/// `1 <= k <= 61` (`s = 61 - k`), and `k >= 62` (`s = 0`); in each the grid step
/// `2^-s` is below `2^-60 · max(1, |x|)`.
pub proof fn lemma_r3_error(n: int, d: int, dir: Dir)
    requires
        d > 0,
        !saturated(n, d),
    ensures
        within_error_bound(round_frac(n, d, dir), n, d),
{
    if exact_path(n, d) {
        lemma_r1_identity(n, d, dir);
        let r = round_frac(n, d, dir);
        assert(r.n() * d - n * r.d() == 0);
        assert(abs_int(0) == 0);
        lemma_pow2_pos(precision_b());
        assert(r.d() * max_int(d, abs_int(n)) >= 0) by (nonlinear_arith)
            requires
                r.d() > 0,
                d > 0,
        ;
    } else {
        lemma_reduce_exact(n, d);
        let g = gcd_int(n, d);
        let rn = red_num(n, d);
        let rd = red_den(n, d);
        let s = snap_shift(rn, rd);
        let sn = grid_num(rn, rd, s, dir);
        let sd = pow2(s);
        lemma_pow2_pos(s);
        lemma_pow2_pos(precision_b());
        lemma_grid_error_step(rn, rd, s, dir);
        lemma_shift_covers_bound(rn, rd);
        lemma_round_frac_wf(n, d, dir);
        lemma_snap_result_fields(n, d, dir);
        let r = round_frac(n, d, dir);
        let g2 = gcd_int(sn, sd);
        // One grid step, scaled: `|sn·rd − rn·2^s| <= rd`, and
        // `rd·2^60 <= 2^s·max(rd, |rn|)` from the shift bound.
        assert(abs_int(sn * rd - rn * sd) * pow2(precision_b()) <= rd * pow2(precision_b()))
            by (nonlinear_arith)
            requires
                abs_int(sn * rd - rn * sd) <= rd,
                pow2(precision_b()) > 0,
        ;
        assert(abs_int(sn * rd - rn * sd) * pow2(precision_b()) <= sd * max_int(rd, abs_int(rn)));
        lemma_error_after_reduce(rn, rd, sn, sd, g2, r);
        lemma_error_scales(n, d, g, rn, rd, r, s);
    }
}

/// One grid step: the snapped numerator is within `1` of the true scaled value,
/// i.e. `|sn·rd - rn·2^s| <= rd`.
pub proof fn lemma_grid_error_step(rn: int, rd: int, s: nat, dir: Dir)
    requires
        rd > 0,
    ensures
        abs_int(grid_num(rn, rd, s, dir) * rd - rn * pow2(s)) <= rd,
{
    let a = rn * pow2(s);
    let q = a / rd;
    let r = a % rd;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(a, rd);
    assert(0 <= r < rd);
    match dir {
        Dir::Down => {
            assert(grid_num(rn, rd, s, dir) == q);
            assert(q * rd - a == -r);
        },
        Dir::Up => {
            let q2 = (-a) / rd;
            let r2 = (-a) % rd;
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(-a, rd);
            assert(0 <= r2 < rd);
            assert(grid_num(rn, rd, s, dir) == -q2);
            assert((-q2) * rd - a == r2) by (nonlinear_arith)
                requires
                    -a == rd * q2 + r2,
            ;
        },
        Dir::Nearest => {
            // Either q or q+1; both are within one step.
            assert(grid_num(rn, rd, s, dir) == q || grid_num(rn, rd, s, dir) == q + 1);
            assert(q * rd - a == -r);
            assert((q + 1) * rd - a == rd - r) by (nonlinear_arith)
                requires
                    a == rd * q + r,
            ;
        },
    }
}

/// The shift is large enough for R3: `rd · 2^60 <= 2^s · max(rd, |rn|)`.
///
/// This is the heart of the bound. `k = bitlen(|rn|/rd)` gives
/// `|rn| >= 2^(k-1) · rd` whenever `k >= 1`, and `s = 61 - k`, so
/// `2^s · |rn| >= 2^(61-k) · 2^(k-1) · rd = 2^60 · rd`. For `k = 0` the shift is
/// `61` and `max(rd, |rn|) >= rd` already suffices.
pub proof fn lemma_shift_covers_bound(rn: int, rd: int)
    requires
        rd > 0,
    ensures
        rd * pow2(precision_b()) <= pow2(snap_shift(rn, rd)) * max_int(rd, abs_int(rn)),
{
    let ip = abs_int(rn) / rd;
    let k = bitlen(ip);
    let s = snap_shift(rn, rd);
    lemma_bitlen_char(ip);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(abs_int(rn), rd);
    // These have to be in the *enclosing* context: a `nonlinear_arith` block
    // sees only its own `requires`, so facts established inside a nested `by`
    // block never reach one.
    lemma_pow2_pos(60nat);
    lemma_pow2_pos(61nat);
    lemma_pow2_pos(s);
    if k == 0 {
        assert(s == 61);
        assert(pow2(61) == 2 * pow2(60));
        assert(max_int(rd, abs_int(rn)) >= rd);
        assert(rd * pow2(60) <= pow2(61) * rd) by (nonlinear_arith)
            requires
                rd > 0,
                pow2(61) == 2 * pow2(60),
                pow2(60) > 0,
        ;
        assert(pow2(61) * rd <= pow2(61) * max_int(rd, abs_int(rn))) by (nonlinear_arith)
            requires
                pow2(61) > 0,
                rd <= max_int(rd, abs_int(rn)),
        ;
    } else {
        // |rn| >= ip * rd >= 2^(k-1) * rd
        assert(abs_int(rn) >= ip * rd) by (nonlinear_arith)
            requires
                abs_int(rn) == rd * ip + abs_int(rn) % rd,
                abs_int(rn) % rd >= 0,
        ;
        assert(pow2((k - 1) as nat) <= ip);
        assert(abs_int(rn) >= pow2((k - 1) as nat) * rd) by (nonlinear_arith)
            requires
                rd > 0,
                abs_int(rn) >= ip * rd,
                pow2((k - 1) as nat) <= ip,
        ;
        if k >= 61 {
            assert(s == 0 && pow2(s) == 1);
            lemma_pow2_mono(60nat, (k - 1) as nat);
            assert(rd * pow2(60) <= pow2((k - 1) as nat) * rd) by (nonlinear_arith)
                requires
                    rd > 0,
                    pow2(60) <= pow2((k - 1) as nat),
            ;
            assert(pow2((k - 1) as nat) * rd <= max_int(rd, abs_int(rn)));
            assert(pow2(s) * max_int(rd, abs_int(rn)) == max_int(rd, abs_int(rn)))
                by (nonlinear_arith)
                requires
                    pow2(s) == 1,
            ;
        } else {
            assert(s == 61 - k);
            crate::model::lemma_pow2_add(s, (k - 1) as nat);
            assert(s + (k - 1) == 60);
            assert(pow2(s) * pow2((k - 1) as nat) == pow2(60));
            assert(rd * pow2(60) <= pow2(s) * abs_int(rn)) by (nonlinear_arith)
                requires
                    rd > 0,
                    pow2(s) > 0,
                    abs_int(rn) >= pow2((k - 1) as nat) * rd,
                    pow2(s) * pow2((k - 1) as nat) == pow2(60),
            ;
            assert(pow2(s) * abs_int(rn) <= pow2(s) * max_int(rd, abs_int(rn)))
                by (nonlinear_arith)
                requires
                    pow2(s) > 0,
                    abs_int(rn) <= max_int(rd, abs_int(rn)),
            ;
        }
    }
}

/// Combine the grid step, the shift bound, and the gcd re-reduction into the
/// division-free R3 statement against the *unreduced* `n / d`.
pub proof fn lemma_error_scales(n: int, d: int, g: int, rn: int, rd: int, r: Q, s: nat)
    requires
        g > 0,
        rd > 0,
        n == rn * g,
        d == rd * g,
        r.d() > 0,
        abs_int(r.n() * rd - rn * r.d()) * pow2(precision_b()) <= r.d() * max_int(rd, abs_int(rn)),
    ensures
        within_error_bound(r, n, d),
{
    assert(r.n() * d - n * r.d() == (r.n() * rd - rn * r.d()) * g) by (nonlinear_arith)
        requires
            n == rn * g,
            d == rd * g,
    ;
    assert(max_int(d, abs_int(n)) == max_int(rd, abs_int(rn)) * g) by (nonlinear_arith)
        requires
            g > 0,
            n == rn * g,
            d == rd * g,
    ;
    assert(abs_int((r.n() * rd - rn * r.d()) * g) == abs_int(r.n() * rd - rn * r.d()) * g)
        by (nonlinear_arith)
        requires
            g > 0,
    ;
    assert(within_error_bound(r, n, d)) by (nonlinear_arith)
        requires
            g > 0,
            r.n() * d - n * r.d() == (r.n() * rd - rn * r.d()) * g,
            max_int(d, abs_int(n)) == max_int(rd, abs_int(rn)) * g,
            abs_int((r.n() * rd - rn * r.d()) * g) == abs_int(r.n() * rd - rn * r.d()) * g,
            abs_int(r.n() * rd - rn * r.d()) * pow2(precision_b()) <= r.d() * max_int(
                rd,
                abs_int(rn),
            ),
    ;
}

// ---------------------------------------------------------------------------
// R4 — monotonicity (stated per grid, as the specification permits)
// ---------------------------------------------------------------------------

/// **R4.** On a fixed grid `2^-s`, snapping is monotone: if `n1/d1 <= n2/d2`
/// then the snapped numerators are ordered the same way, in every direction.
///
/// Stated per-grid. The *composed* operation ("return exactly if it fits,
/// otherwise snap") is **not** globally monotone — see the counterexample in
/// `README.md` — and this crate does not claim that it is.
pub proof fn lemma_r4_monotone_grid(n1: int, d1: int, n2: int, d2: int, s: nat, dir: Dir)
    requires
        d1 > 0,
        d2 > 0,
        n1 * d2 <= n2 * d1,
    ensures
        grid_num(n1, d1, s, dir) * d2 * d1 <= grid_num(n2, d2, s, dir) * d1 * d2,
{
    lemma_pow2_pos(s);
    // The scaled values are ordered: (n1·2^s)/d1 <= (n2·2^s)/d2.
    assert((n1 * pow2(s)) * d2 <= (n2 * pow2(s)) * d1) by (nonlinear_arith)
        requires
            n1 * d2 <= n2 * d1,
            pow2(s) > 0,
    ;
    lemma_round_int_monotone(n1 * pow2(s), d1, n2 * pow2(s), d2, dir);
}

/// Rounding a rational to an integer in a fixed direction is monotone.
pub proof fn lemma_round_int_monotone(a1: int, d1: int, a2: int, d2: int, dir: Dir)
    requires
        d1 > 0,
        d2 > 0,
        a1 * d2 <= a2 * d1,
    ensures
        ({
            let q1 = round_int(a1, d1, dir);
            let q2 = round_int(a2, d2, dir);
            q1 * d2 * d1 <= q2 * d1 * d2
        }),
{
    // floor, ceil and nearest-ties-even are each monotone as functions of the
    // real value; since a1/d1 <= a2/d2, the rounded integers are ordered.
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(a1, d1);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(a2, d2);
    let q1 = round_int(a1, d1, dir);
    let q2 = round_int(a2, d2, dir);
    match dir {
        Dir::Down => {
            lemma_floor_div_monotone(a1, d1, a2, d2);
        },
        Dir::Up => {
            // Ceiling is floor of the negation, negated, and negating flips
            // the hypothesis.
            assert((-a2) * d1 <= (-a1) * d2) by (nonlinear_arith)
                requires
                    a1 * d2 <= a2 * d1,
            ;
            lemma_floor_div_monotone(-a2, d2, -a1, d1);
        },
        Dir::Nearest => {
            lemma_floor_div_monotone(a1, d1, a2, d2);
            let f1 = a1 / d1;
            let f2 = a2 / d2;
            let r1 = a1 % d1;
            let r2 = a2 % d2;
            // When the floors differ the result is immediate, because each
            // rounded value lies in {floor, floor + 1}. When they agree, the
            // fractional parts are ordered, and the tie rule is monotone in
            // them: `2r > d` and `2r == d` both propagate upwards.
            if f1 == f2 {
                assert(r1 * d2 <= r2 * d1) by (nonlinear_arith)
                    requires
                        a1 == d1 * f1 + r1,
                        a2 == d2 * f2 + r2,
                        f1 == f2,
                        a1 * d2 <= a2 * d1,
                ;
                assert(2 * r1 > d1 ==> 2 * r2 > d2) by (nonlinear_arith)
                    requires
                        d1 > 0,
                        d2 > 0,
                        r1 * d2 <= r2 * d1,
                ;
                assert(2 * r1 == d1 ==> 2 * r2 >= d2) by (nonlinear_arith)
                    requires
                        d1 > 0,
                        d2 > 0,
                        r1 * d2 <= r2 * d1,
                ;
            }
        },
    }
    assert(q1 <= q2);
    assert(q1 * d2 * d1 <= q2 * d1 * d2) by (nonlinear_arith)
        requires
            d1 > 0,
            d2 > 0,
            q1 <= q2,
    ;
}

/// The direction-independent kernel used by [`grid_num`], factored out so
/// monotonicity can be stated once.
pub open spec fn round_int(a: int, d: int, dir: Dir) -> int {
    match dir {
        Dir::Down => a / d,
        Dir::Up => -((-a) / d),
        Dir::Nearest => {
            let q = a / d;
            let r = a % d;
            if 2 * r > d {
                q + 1
            } else if 2 * r < d {
                q
            } else if q % 2 == 0 {
                q
            } else {
                q + 1
            }
        },
    }
}

/// Floor division is monotone across different positive denominators.
pub proof fn lemma_floor_div_monotone(a1: int, d1: int, a2: int, d2: int)
    requires
        d1 > 0,
        d2 > 0,
        a1 * d2 <= a2 * d1,
    ensures
        a1 / d1 <= a2 / d2,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(a1, d1);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(a2, d2);
    let q1 = a1 / d1;
    let r1 = a1 % d1;
    let q2 = a2 / d2;
    let r2 = a2 % d2;
    assert(0 <= r1 < d1 && 0 <= r2 < d2);
    // q1 <= a1/d1 <= a2/d2 < q2 + 1, hence q1 <= q2.
    assert(q1 * (d1 * d2) <= a1 * d2) by (nonlinear_arith)
        requires
            a1 == d1 * q1 + r1,
            0 <= r1,
            d2 > 0,
    ;
    assert(a2 * d1 < (q2 + 1) * (d1 * d2)) by (nonlinear_arith)
        requires
            a2 == d2 * q2 + r2,
            r2 < d2,
            d1 > 0,
    ;
    assert(q1 < q2 + 1) by (nonlinear_arith)
        requires
            d1 > 0,
            d2 > 0,
            q1 * (d1 * d2) <= a1 * d2,
            a1 * d2 <= a2 * d1,
            a2 * d1 < (q2 + 1) * (d1 * d2),
    ;
}

// ---------------------------------------------------------------------------
// Executable helpers
// ---------------------------------------------------------------------------

/// `2^s` as an `i128`.
pub fn pow2_i128(s: u32) -> (r: i128)
    requires
        s <= 126,
    ensures
        r == pow2(s as nat),
        r > 0,
{
    let mut p: i128 = 1;
    let mut i: u32 = 0;
    proof {
        lemma_pow2_pos(126nat);
        crate::model::lemma_pow2_126();
    }
    while i < s
        invariant
            i <= s,
            s <= 126,
            p == pow2(i as nat),
            p > 0,
            // The literal is what discharges the `i128` overflow check on
            // `p * 2`; `p <= pow2(126)` alone tells the solver nothing about
            // the machine type.
            p <= 85070591730234615865843651857942052864,
        decreases s - i,
    {
        proof {
            lemma_pow2_mono((i + 1) as nat, 126nat);
            lemma_pow2_pos((i + 1) as nat);
            crate::model::lemma_pow2_126();
            crate::model::lemma_pow2_125();
            lemma_pow2_mono(i as nat, 125nat);
        }
        p = p * 2;
        i = i + 1;
    }
    p
}

/// Bit length of a non-negative `i128`: the least `k` with `x < 2^k`.
pub fn bitlen_i128(x: i128) -> (k: u32)
    requires
        0 <= x,
        x < pow2(126),
    ensures
        k as nat == bitlen(x as int),
        k <= 126,
{
    let mut p: i128 = 1;
    let mut k: u32 = 0;
    proof {
        lemma_pow2_pos(0nat);
        crate::model::lemma_pow2_126();
    }
    while p <= x
        invariant
            p == pow2(k as nat),
            p > 0,
            k <= 126,
            x < pow2(126),
            // Literal, for the same reason as in `pow2_i128`: inside the loop
            // `p <= x < 2^126`, so `p * 2 < 2^127` and the doubling is safe.
            x <= 85070591730234615865843651857942052864,
            forall|j: nat| j < k as nat ==> pow2(j) <= x,
        // `x - p` is not a legal measure: it is only non-negative while the
        // guard holds, and Verus checks the *decremented* value. `126 - k` is
        // non-negative because `p == 2^k <= x < 2^126` forces `k < 126`.
        decreases 126 - k,
    {
        proof {
            if k >= 126 {
                lemma_pow2_mono(126nat, k as nat);
            }
            assert(k < 126);
            lemma_pow2_mono((k + 1) as nat, 126nat);
            lemma_pow2_pos((k + 1) as nat);
            crate::model::lemma_pow2_126();
            assert(p * 2 > p) by (nonlinear_arith)
                requires
                    p > 0,
            ;
        }
        p = p * 2;
        k = k + 1;
    }
    proof {
        lemma_bitlen_char(x as int);
        lemma_bitlen_unique(x as int, k as nat);
    }
    k
}

/// `bitlen` is characterised by `2^(k-1) <= x < 2^k`, so any `k` with that
/// property is *the* bit length.
pub proof fn lemma_bitlen_unique(x: int, k: nat)
    requires
        0 <= x,
        x < pow2(k),
        forall|j: nat| j < k ==> pow2(j) <= x,
    ensures
        bitlen(x) == k,
{
    lemma_bitlen_char(x);
    let b = bitlen(x);
    if b < k {
        assert(pow2(b) <= x);
        assert(x < pow2(b));
    }
    if b > k {
        assert(pow2((b - 1) as nat) <= x);
        lemma_pow2_mono(k, (b - 1) as nat);
    }
}

/// `floor(n · 2^s / d)` and its remainder, computed **without ever forming
/// `n · 2^s`** — which would overflow `i128` for the denominators this crate
/// sees.
///
/// The loop carries `q` (bounded by `2^62` via the precondition) and `rem`
/// (bounded by `d`), so the widest live value is `2 · rem < 2 · 2^124 = 2^125`.
pub fn shift_div(n: i128, d: i128, s: u32) -> (res: (i128, i128))
    requires
        0 <= n,
        0 < d,
        s <= 61,
        d <= pow2(124),
        n * pow2(s as nat) < d * pow2(62),
    ensures
        res.0 * d + res.1 == n * pow2(s as nat),
        0 <= res.1 < d,
        0 <= res.0,
        res.0 < pow2(62),
{
    let mut q: i128 = n / d;
    let mut rem: i128 = n % d;
    let mut i: u32 = 0;
    proof {
        lemma_pow2_pos(62nat);
        lemma_pow2_pos(124nat);
        crate::model::lemma_pow2_62();
        crate::model::lemma_pow2_124();
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(n as int, d as int);
        crate::model::lemma_pow2_small();
        assert(pow2(i as nat) <= pow2(s as nat)) by {
            lemma_pow2_mono(i as nat, s as nat);
        }
        assert((n as int) * pow2(0nat) == n as int) by (nonlinear_arith)
            requires
                pow2(0nat) == 1,
        ;
        assert((n as int) == (d as int) * (q as int) + (rem as int));
        assert(q * d + rem == n * pow2(0nat));
        lemma_quotient_bound(q as int, rem as int, d as int, n as int, 0nat, s as nat);
    }
    while i < s
        invariant
            i <= s,
            s <= 61,
            0 < d <= pow2(124),
            q * d + rem == n * pow2(i as nat),
            0 <= rem < d,
            0 <= q,
            q < pow2(62),
            n * pow2(s as nat) < d * pow2(62),
            0 <= n,
            // Literal forms of the two bounds above. `rem < d <= 2^124` makes
            // `rem * 2 < 2^125` safe, and `q < 2^62` makes `q * 2 + 1` safe;
            // stated with `pow2` they discharge neither.
            d <= 21267647932558653966460912964485513216,
            q < 4611686018427387904,
        decreases s - i,
    {
        proof {
            lemma_pow2_pos(124nat);
            crate::model::lemma_pow2_62();
            crate::model::lemma_pow2_124();
        }
        let ghost q_old: int = q as int;
        let ghost rem_old: int = rem as int;
        rem = rem * 2;
        q = q * 2;
        if rem >= d {
            rem = rem - d;
            q = q + 1;
        }
        i = i + 1;
        proof {
            crate::model::lemma_pow2_add(1nat, (i - 1) as nat);
            crate::model::lemma_pow2_small();
            assert(pow2(i as nat) == 2 * pow2((i - 1) as nat));
            // Doubling the carried identity: `(2q)·d == 2·(q·d)` is nonlinear,
            // and outside a nonlinear block the two are unrelated terms.
            assert((2 * q_old) * (d as int) == 2 * (q_old * (d as int))) by (nonlinear_arith);
            assert((2 * q_old + 1) * (d as int) == 2 * (q_old * (d as int)) + (d as int))
                by (nonlinear_arith);
            assert(2 * (q_old * (d as int) + rem_old) == 2 * (q_old * (d as int)) + 2 * rem_old);
            // Doubling both sides of the carried identity is nonlinear in `n`.
            assert(2 * ((n as int) * pow2((i - 1) as nat)) == (n as int) * (2 * pow2(
                (i - 1) as nat,
            ))) by (nonlinear_arith);
            lemma_quotient_bound(q as int, rem as int, d as int, n as int, i as nat, s as nat);
            crate::model::lemma_pow2_62();
        }
    }
    (q, rem)
}

/// If `q·d + rem == n·2^i` with `0 <= rem < d` and `n·2^s < d·2^62` for some
/// `s >= i`, then `q < 2^62`.
pub proof fn lemma_quotient_bound(q: int, rem: int, d: int, n: int, i: nat, s: nat)
    requires
        d > 0,
        0 <= rem < d,
        0 <= n,
        i <= s,
        q * d + rem == n * pow2(i),
        n * pow2(s) < d * pow2(62),
    ensures
        0 <= q,
        q < pow2(62),
{
    lemma_pow2_pos(i);
    lemma_pow2_pos(s);
    lemma_pow2_mono(i, s);
    assert(n * pow2(i) <= n * pow2(s)) by (nonlinear_arith)
        requires
            n >= 0,
            pow2(i) <= pow2(s),
    ;
    assert(q * d < d * pow2(62)) by (nonlinear_arith)
        requires
            q * d + rem == n * pow2(i),
            rem >= 0,
            n * pow2(i) <= n * pow2(s),
            n * pow2(s) < d * pow2(62),
    ;
    assert(q < pow2(62)) by (nonlinear_arith)
        requires
            d > 0,
            q * d < d * pow2(62),
    ;
    assert(q >= 0) by (nonlinear_arith)
        requires
            d > 0,
            rem < d,
            n >= 0,
            pow2(i) > 0,
            q * d + rem == n * pow2(i),
    ;
}

// ---------------------------------------------------------------------------
// The executable rounding entry point
// ---------------------------------------------------------------------------

/// The bound every caller must respect on the numerator handed to
/// [`round_frac_exec`]: `2^126`. All of this crate's intermediates are below
/// `2^125`.
pub open spec fn num_input_bound() -> int {
    pow2(126)
}

/// The bound every caller must respect on the denominator: `2^124`.
pub open spec fn den_input_bound() -> int {
    pow2(124)
}

/// Canonicalise (and, if necessary, round) the exact fraction `n / d`.
///
/// This is the single place where an exact `i128` intermediate becomes a `Q`.
/// Every arithmetic operation in [`crate::q`] ends here.
pub fn round_frac_exec(n: i128, d: i128, dir: Dir) -> (r: Q)
    requires
        d > 0,
        abs_int(n as int) < num_input_bound(),
        d as int <= den_input_bound(),
    ensures
        r.wf(),
        r == round_frac(n as int, d as int, dir),
{
    proof {
        // The input bounds are stated with `pow2`, which discharges no `i128`
        // overflow or range check on its own; pin the two literals down first.
        crate::model::lemma_pow2_124();
        crate::model::lemma_pow2_126();
        crate::model::lemma_max_mag_pow2();
        // Every branch that returns a denominator of one — zero and both
        // saturating cases — needs this.
        lemma_gcd_one();
        lemma_round_frac_wf(n as int, d as int, dir);
    }
    if n == 0 {
        return Q { num: 0, den: 1 };
    }
    let m0: i128 = if n < 0 {
        0 - n
    } else {
        n
    };
    let ip0: i128 = m0 / d;
    let fr0: i128 = m0 % d;
    let mm: i128 = MAX_MAG as i128;
    if ip0 > mm || (ip0 == mm && fr0 != 0) {
        proof {
            lemma_magnitude_test(m0 as int, d as int, ip0 as int, fr0 as int);
        }
        if n > 0 {
            return Q { num: MAX_MAG, den: 1 };
        } else {
            return Q { num: -MAX_MAG, den: 1 };
        }
    }
    proof {
        lemma_magnitude_test(m0 as int, d as int, ip0 as int, fr0 as int);
    }
    let g: i128 = gcd_abs_i128(n, d);
    proof {
        // `red_den > 0` (hence `g <= d`, hence the divisions below are safe) and
        // the two exactness equations `n == rn·g`, `d == rd·g`.
        lemma_reduce_exact(n as int, d as int);
        lemma_gcd_reduce_coprime(abs_int(n as int) as nat, d as nat);
        lemma_reduce_abs(n as int, d as int);
        lemma_reduce_magnitude_fits(n as int, d as int);
        // The reduction equations come out as `x == r·g`; the quotient lemma
        // wants `g·r`, and outside a nonlinear block those are distinct terms.
        assert((g as int) * red_num(n as int, d as int) == red_num(n as int, d as int) * (
        g as int)) by (nonlinear_arith);
        assert((g as int) * red_den(n as int, d as int) == red_den(n as int, d as int) * (
        g as int)) by (nonlinear_arith);
        assert((g as int) * abs_int(red_num(n as int, d as int)) == abs_int(
            red_num(n as int, d as int),
        ) * (g as int)) by (nonlinear_arith);
        // I1's zero clause on the exact-path return below: `n != 0` and
        // `n == rn·g` force `rn != 0`, so the clause is vacuous.
        assert(red_num(n as int, d as int) != 0) by (nonlinear_arith)
            requires
                n != 0,
                (n as int) == red_num(n as int, d as int) * (g as int),
        ;
    }
    let rn: i128 = n / g;
    let rd: i128 = d / g;
    let arn: i128 = if rn < 0 {
        0 - rn
    } else {
        rn
    };
    if arn <= mm && rd <= mm {
        return Q { num: rn as i64, den: rd as i64 };
    }
    // --- dyadic snap -------------------------------------------------------
    proof {
        vstd::arithmetic::div_mod::lemma_div_pos_is_pos(arn as int, rd as int);
    }
    let ip: i128 = arn / rd;
    let k: u32 = bitlen_i128(ip);
    let s: u32 = if k >= 61 {
        0
    } else {
        61 - k
    };
    proof {
        // The overflow test above bounded `|n| / d`; the shift is chosen from
        // `arn / rd`. Reduction does not move the integer part, so the bound
        // carries across.
        lemma_reduce_quotient(m0 as int, d as int, g as int, arn as int, rd as int);
        lemma_shift_div_precondition(arn as int, rd as int, s as nat, k as nat);
    }
    let (qf, rf) = shift_div(arn, rd, s);
    let neg: bool = rn < 0;
    let qm: i128 = match dir {
        Dir::Down => if neg {
            if rf > 0 {
                qf + 1
            } else {
                qf
            }
        } else {
            qf
        },
        Dir::Up => if neg {
            qf
        } else {
            if rf > 0 {
                qf + 1
            } else {
                qf
            }
        },
        Dir::Nearest => {
            let t: i128 = rf * 2;
            if t > rd || (t == rd && qf % 2 != 0) {
                qf + 1
            } else {
                qf
            }
        },
    };
    let sn: i128 = if neg {
        0 - qm
    } else {
        qm
    };
    let sd: i128 = pow2_i128(s);
    proof {
        lemma_grid_num_matches(rn as int, rd as int, s as nat, dir, qf as int, rf as int, sn as int);
        // `lemma_snap_in_budget` wants the one-grid-step bound on `|sn|`, which
        // is `lemma_snap_magnitude`'s conclusion.
        lemma_snap_magnitude(rn as int, rd as int, s as nat, dir);
        lemma_snap_in_budget(rn as int, rd as int, s as nat, sn as int, k as nat);
    }
    let g2: i128 = gcd_abs_i128(sn, sd);
    let on: i128 = sn / g2;
    let od: i128 = sd / g2;
    proof {
        lemma_reduce_exact(sn as int, sd as int);
        lemma_gcd_reduce_coprime(abs_int(sn as int) as nat, sd as nat);
    }
    Q { num: on as i64, den: od as i64 }
}

/// `|n| <= MAX_MAG · d` is exactly `ip < MAX_MAG || (ip == MAX_MAG && fr == 0)`
/// for `ip = |n| / d`, `fr = |n| % d` — the overflow test without ever forming
/// `MAX_MAG · d` (which would overflow `i128`).
pub proof fn lemma_magnitude_test(m: int, d: int, ip: int, fr: int)
    requires
        d > 0,
        m >= 0,
        ip == m / d,
        fr == m % d,
    ensures
        (m <= max_mag() * d) <==> (ip < max_mag() || (ip == max_mag() && fr == 0)),
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(m, d);
    assert(0 <= fr < d);
    assert(m == d * ip + fr);
    assert((ip < max_mag()) ==> m < max_mag() * d) by (nonlinear_arith)
        requires
            d > 0,
            m == d * ip + fr,
            0 <= fr < d,
    ;
    assert((ip > max_mag()) ==> m > max_mag() * d) by (nonlinear_arith)
        requires
            d > 0,
            m == d * ip + fr,
            0 <= fr,
    ;
    // The boundary case `ip == max_mag()` is the one the two implications above
    // leave open: there `m == max_mag()·d + fr`, so `m <= max_mag()·d` holds
    // exactly when `fr == 0`. Commuting the product is all Z3 needs to see it.
    assert(d * ip == ip * d) by (nonlinear_arith);
}

/// Reducing a fraction by a common divisor leaves its integer part alone:
/// `(g·rm) / (g·rd) == rm / rd`.
///
/// The overflow test in [`round_frac_exec`] runs on the *unreduced* pair, but
/// the shift is chosen from the *reduced* one; this is what lets the first
/// bound travel to the second.
pub proof fn lemma_reduce_quotient(m: int, d: int, g: int, rm: int, rd: int)
    requires
        g > 0,
        rd > 0,
        rm >= 0,
        m == g * rm,
        d == g * rd,
    ensures
        m / d == rm / rd,
{
    let q = rm / rd;
    let r = rm % rd;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(rm, rd);
    assert(0 <= r < rd);
    // `m == d·q + g·r` with `0 <= g·r < g·rd == d`, which pins `m / d` to `q`.
    assert(m == d * q + g * r) by (nonlinear_arith)
        requires
            m == g * rm,
            d == g * rd,
            rm == rd * q + r,
    ;
    assert(0 <= g * r < d) by (nonlinear_arith)
        requires
            g > 0,
            0 <= r < rd,
            d == g * rd,
    ;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(m, d, q, g * r);
}

/// Reduction preserves representability: if `|n| <= MAX_MAG·d` then
/// `|rn| <= MAX_MAG·rd`.
///
/// Both `lemma_round_frac_wf` and [`round_frac_exec`] test the magnitude on the
/// unreduced pair but hand the reduced one to `lemma_snap_in_budget`.
pub proof fn lemma_reduce_magnitude_fits(n: int, d: int)
    requires
        d > 0,
        magnitude_fits(n, d),
    ensures
        magnitude_fits(red_num(n, d), red_den(n, d)),
{
    let g = gcd_int(n, d);
    let rn = red_num(n, d);
    let rd = red_den(n, d);
    lemma_reduce_exact(n, d);
    lemma_reduce_abs(n, d);
    assert(abs_int(rn) * g <= (max_mag() * rd) * g) by (nonlinear_arith)
        requires
            abs_int(n) == abs_int(rn) * g,
            d == rd * g,
            abs_int(n) <= max_mag() * d,
    ;
    assert(abs_int(rn) <= max_mag() * rd) by (nonlinear_arith)
        requires
            g > 0,
            abs_int(rn) * g <= (max_mag() * rd) * g,
    ;
}

/// The `shift_div` precondition holds for the shift the algorithm picks.
pub proof fn lemma_shift_div_precondition(m: int, rd: int, s: nat, k: nat)
    requires
        rd > 0,
        m >= 0,
        k == bitlen(m / rd),
        s == (if k >= 61 { 0nat } else { (61 - k) as nat }),
        m / rd <= max_mag(),
    ensures
        m * pow2(s) < rd * pow2(62),
{
    let ip = m / rd;
    lemma_bitlen_char(ip);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(m, rd);
    assert(m < (ip + 1) * rd) by (nonlinear_arith)
        requires
            m == rd * ip + m % rd,
            0 <= m % rd < rd,
    ;
    if k >= 61 {
        assert(s == 0 && pow2(s) == 1);
        // `ip <= max_mag()` is a hypothesis, and `max_mag() == 2^62 - 1`; the
        // bound is unreachable without that identity.
        assert(ip + 1 <= pow2(62)) by {
            crate::model::lemma_max_mag_pow2();
        }
        assert(m * 1 < rd * pow2(62)) by (nonlinear_arith)
            requires
                rd > 0,
                m < (ip + 1) * rd,
                ip + 1 <= pow2(62),
        ;
    } else {
        assert(ip < pow2(k));
        assert(ip + 1 <= pow2(k));
        crate::model::lemma_pow2_add(s, k);
        assert(s + k == 61);
        assert(pow2(s) * pow2(k) == pow2(61));
        lemma_pow2_pos(s);
        lemma_pow2_pos(k);
        assert(m * pow2(s) < rd * pow2(61)) by (nonlinear_arith)
            requires
                rd > 0,
                pow2(s) > 0,
                m < (ip + 1) * rd,
                ip + 1 <= pow2(k),
                pow2(s) * pow2(k) == pow2(61),
        ;
        assert(pow2(61) <= pow2(62)) by {
            lemma_pow2_mono(61nat, 62nat);
        }
        assert(rd * pow2(61) <= rd * pow2(62)) by (nonlinear_arith)
            requires
                rd > 0,
                pow2(61) <= pow2(62),
        ;
    }
}

/// The magnitude-based executable snap agrees with the signed
/// [`grid_num`] specification.
pub proof fn lemma_grid_num_matches(rn: int, rd: int, s: nat, dir: Dir, qf: int, rf: int, sn: int)
    requires
        rd > 0,
        qf * rd + rf == abs_int(rn) * pow2(s),
        0 <= rf < rd,
        sn == (if rn < 0 {
            match dir {
                Dir::Down => if rf > 0 { -(qf + 1) } else { -qf },
                Dir::Up => -qf,
                Dir::Nearest => if 2 * rf > rd || (2 * rf == rd && qf % 2 != 0) {
                    -(qf + 1)
                } else {
                    -qf
                },
            }
        } else {
            match dir {
                Dir::Down => qf,
                Dir::Up => if rf > 0 { qf + 1 } else { qf },
                Dir::Nearest => if 2 * rf > rd || (2 * rf == rd && qf % 2 != 0) {
                    qf + 1
                } else {
                    qf
                },
            }
        }),
    ensures
        sn == grid_num(rn, rd, s, dir),
{
    let a = rn * pow2(s);
    lemma_pow2_pos(s);
    // Outside a `nonlinear_arith` block multiplication is uninterpreted, so
    // `qf * rd` and `rd * qf` are different terms to the solver — and
    // `lemma_fundamental_div_mod_converse` wants the divisor first.
    assert(rd * qf == qf * rd) by (nonlinear_arith);
    if rn >= 0 {
        assert(a == abs_int(rn) * pow2(s));
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(a, rd, qf, rf);
        assert(a / rd == qf && a % rd == rf);
        // `Up` is specified as `-((-a) / rd)`, so the negated quotient is
        // needed here too — it is `-qf` on the nose and `-(qf + 1)` otherwise.
        if rf == 0 {
            assert(-a == rd * (-qf) + 0) by (nonlinear_arith)
                requires
                    a == rd * qf + 0,
            ;
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(-a, rd, -qf, 0);
        } else {
            assert(-a == rd * (-(qf + 1)) + (rd - rf)) by (nonlinear_arith)
                requires
                    a == rd * qf + rf,
            ;
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
                -a,
                rd,
                -(qf + 1),
                rd - rf,
            );
        }
    } else {
        // `a` is a `let`-bound local, and a `nonlinear_arith` block sees only
        // its own `requires` — so its definition has to be restated here.
        assert(-a == abs_int(rn) * pow2(s)) by (nonlinear_arith)
            requires
                a == rn * pow2(s),
                abs_int(rn) == -rn,
        ;
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(-a, rd, qf, rf);
        assert((-a) / rd == qf && (-a) % rd == rf);
        if rf == 0 {
            assert(a == rd * (-qf) + 0) by (nonlinear_arith)
                requires
                    -a == rd * qf + 0,
            ;
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(a, rd, -qf, 0);
        } else {
            assert(a == rd * (-(qf + 1)) + (rd - rf)) by (nonlinear_arith)
                requires
                    -a == rd * qf + rf,
            ;
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
                a,
                rd,
                -(qf + 1),
                rd - rf,
            );
            // `Nearest`'s tie rule is stated on the parity of the *floor*,
            // which for a negative value is `-(qf + 1)` — the opposite parity
            // to `qf`. That flip is exactly why the specification's tie test
            // reads `qf % 2 != 0` rather than `== 0`.
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(qf, 2);
            if qf % 2 == 0 {
                vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
                    -(qf + 1),
                    2,
                    -(qf / 2) - 1,
                    1,
                );
            } else {
                vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
                    -(qf + 1),
                    2,
                    -(qf / 2) - 1,
                    0,
                );
            }
        }
    }
}

/// The snapped numerator and denominator both fit the budget.
///
/// Denominator: `2^s <= 2^61 <= MAX_MAG`.
///
/// Numerator, for `k <= 60`: `s = 61 - k` and `|rn| < 2^k·rd`, so the snapped
/// quotient is below `2^61` and one more than it still fits.
///
/// Numerator, for `k >= 61` (shift clamped to `0`): the result is `ceil(|x|)`,
/// so it is enough that `floor(|x|) < MAX_MAG`. If it were equal, then
/// `|rn| == MAX_MAG·rd` exactly, so `rd` divides `|rn|`; coprimality forces
/// `rd == 1`, and then `|rn| == MAX_MAG` means the pair *did* fit the budget —
/// contradicting the hypothesis that it did not. That is why coprimality is a
/// precondition here: without it the bound is simply false.
pub proof fn lemma_snap_in_budget(rn: int, rd: int, s: nat, sn: int, k: nat)
    requires
        rd > 0,
        rn != 0,
        gcd_int(rn, rd) == 1,
        abs_int(rn) <= max_mag() * rd,
        !fits_budget(rn, rd),
        k == bitlen(abs_int(rn) / rd),
        s == (if k >= 61 { 0nat } else { (61 - k) as nat }),
        abs_int(sn) <= abs_int(rn) * pow2(s) / rd + 1,
    ensures
        abs_int(sn) <= max_mag(),
        pow2(s) <= max_mag(),
{
    crate::model::lemma_max_mag_pow2();
    lemma_pow2_pos(s);
    lemma_pow2_mono(s, 61nat);
    let ip = abs_int(rn) / rd;
    let m = abs_int(rn) * pow2(s);
    let q = m / rd;
    lemma_bitlen_char(ip);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(abs_int(rn), rd);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(m, rd);
    assert(abs_int(rn) == rd * ip + abs_int(rn) % rd);
    assert(m == rd * q + m % rd);
    if k >= 61 {
        assert(s == 0 && pow2(s) == 1);
        assert(m == abs_int(rn));
        assert(q == ip);
        // ip <= max_mag from the magnitude hypothesis.
        assert(ip <= max_mag()) by (nonlinear_arith)
            requires
                rd > 0,
                abs_int(rn) <= max_mag() * rd,
                abs_int(rn) == rd * ip + abs_int(rn) % rd,
                abs_int(rn) % rd >= 0,
        ;
        // Strictness: equality would make rd divide |rn|.
        if ip == max_mag() {
            assert(abs_int(rn) == max_mag() * rd) by (nonlinear_arith)
                requires
                    rd > 0,
                    ip == max_mag(),
                    abs_int(rn) <= max_mag() * rd,
                    abs_int(rn) == rd * ip + abs_int(rn) % rd,
                    abs_int(rn) % rd >= 0,
            ;
            assert(abs_int(rn) == rd * max_mag()) by (nonlinear_arith)
                requires
                    abs_int(rn) == max_mag() * rd,
            ;
            assert(divides(rd, abs_int(rn)));
            lemma_coprime_forces_unit(rn, rd);
            assert(rd == 1);
            assert(abs_int(rn) == max_mag());
            assert(fits_budget(rn, rd));
        }
    } else {
        assert(s == 61 - k);
        crate::model::lemma_pow2_add(s, k);
        assert(pow2(s) * pow2(k) == pow2(61));
        lemma_pow2_pos(k);
        // |rn| < (ip + 1)·rd <= 2^k·rd
        assert(abs_int(rn) < (ip + 1) * rd) by (nonlinear_arith)
            requires
                abs_int(rn) == rd * ip + abs_int(rn) % rd,
                0 <= abs_int(rn) % rd < rd,
        ;
        assert(ip + 1 <= pow2(k));
        assert(abs_int(rn) < pow2(k) * rd) by (nonlinear_arith)
            requires
                rd > 0,
                abs_int(rn) < (ip + 1) * rd,
                ip + 1 <= pow2(k),
        ;
        // q·rd <= m == |rn|·2^s < 2^k·rd·2^s == 2^61·rd, so q < 2^61.
        assert(q * rd <= m) by (nonlinear_arith)
            requires
                m == rd * q + m % rd,
                m % rd >= 0,
        ;
        assert(m < pow2(61) * rd) by (nonlinear_arith)
            requires
                rd > 0,
                pow2(s) > 0,
                m == abs_int(rn) * pow2(s),
                abs_int(rn) < pow2(k) * rd,
                pow2(s) * pow2(k) == pow2(61),
        ;
        assert(q < pow2(61)) by (nonlinear_arith)
            requires
                rd > 0,
                q * rd <= m,
                m < pow2(61) * rd,
        ;
    }
}

/// A reduced fraction whose denominator divides its numerator has denominator
/// one.
pub proof fn lemma_coprime_forces_unit(rn: int, rd: int)
    requires
        rd > 0,
        gcd_int(rn, rd) == 1,
        divides(rd, abs_int(rn)),
    ensures
        rd == 1,
{
    // `divides(rd, rd)` is a precondition of `lemma_gcd_greatest`, so it has to
    // be in scope *before* the call, not after it.
    crate::model::lemma_divides_basic(rd);
    crate::gcd::lemma_gcd_greatest(abs_int(rn) as nat, rd as nat, rd);
    crate::model::lemma_divides_le(rd, 1);
}

} // verus!
