//! The rounding contract R1–R4 (obligation V4), and the single canonicalising
//! entry point that every arithmetic operation uses.
//!
//! # The algorithm
//!
//! [`round_frac_exec`] takes an *exact* fraction `n / d` computed in `i128` and
//! produces the `Rat` that the operation returns:
//!
//! 1. `n == 0` → `0/1`.
//! 2. `|n/d| > MAX_MAG` → **saturate** to `±MAX_MAG/1`. R3 does not apply
//!    outside the representable range. This is a choice, not a necessity, as
//!    `model::magnitude_fits` explains. The `checked_*` operations instead
//!    surface this case as `None`.
//! 3. Reduce by `gcd(|n|, d)`. If the reduced pair fits the budget, return it
//!    **exactly**. This is R1. Thus small investigations pay zero rounding.
//! 4. Otherwise **dyadic snap**: pick a shift `s`, round `n·2^s / d` to an
//!    integer in the requested direction, and return that over `2^s`
//!    (re-reduced).
//!
//! # Choosing the shift
//!
//! With `k = bitlen(floor(|x|))` (so `2^(k-1) <= |x| < 2^k` for `|x| >= 1`, and
//! `k = 0` for `|x| < 1`), the shift is `s = 62 - k`, capped at `61` and
//! floored at `0`.
//!
//! * The grid step is `2^-s`, which is `2^(k-62)` for `k >= 1` and `2^-61` at
//!   the cap (`k == 0`).
//! * The bound R3 demands is `2^-61 · max(1, |x|)`: that is `2^-61` for
//!   `|x| < 1`, and `>= 2^-61 · 2^(k-1) = 2^(k-62)` above.
//!
//! The two meet exactly in both regimes. Therefore **`B = 61` holds for the
//! directed modes**, one bit better than the specification's `B >= 60` bar.
//!
//! `Dir::Nearest` is a half grid step, and every default operation uses it.
//! It therefore satisfies `B = 62`. The uniform R3 contract stays at `B = 61`
//! for all three directions, because the directed modes achieve no better.
//! `Dir::Nearest` additionally carries the tighter bound as its own guarantee.
//! `lemma_grid_error_step_nearest_half` is the half-step form (division-free:
//! `2·|sn·rd − rn·2^s| <= rd`), `lemma_r3_error_nearest` composes it into the
//! full bound, and `Rat::add`/`sub`/`mul`/`div` each `ensures` it alongside
//! the uniform one.
//!
//! # Why the shift is `62 - k` and not `61 - k`
//!
//! A shift of `61 - k` reserves a bit of headroom. It gives `|x| · 2^s < 2^61`,
//! thus a rounding carry can never push the numerator past the budget. That
//! costs a bit of precision to avoid a case that is cheap to handle directly.
//!
//! A shift of `62 - k` spends the whole budget. It gives
//! `|x| · 2^s < 2^k · 2^(62-k) = 2^62`, thus rounding up can land on `2^62`
//! exactly, one past `MAX_MAG`. That case is the *carry*, and it costs nothing.
//! The pair is then `±2^62 / 2^s` with `s >= 1`, and `2^s` divides `2^62`.
//! The reduction that every operation already performs thus turns it into
//! `±2^(62-s) / 1`, comfortably inside I2. The proof is `lemma_carry_reduces`
//! (no intra-doc link: items inside `verus!` are not resolvable from module
//! docs). The cap at `s <= 61` keeps the *denominator* `2^s` inside the budget
//! in the `k == 0` case, where no carry is possible.
//!
//! Ties break to even, as IEEE-754 does. Long fold chains thus do not drift in
//! a fixed direction.
//!
//! # No overflow (V2)
//!
//! The code *never* materialises `n·2^s`, because that overflows `i128`.
//! [`shift_div`] instead walks `s <= 61` doubling steps. It carries only a
//! quotient (`< 2^62`) and a remainder (`< d <= 2^124`), so the widest live
//! value is `2·d < 2^125`.

use verus_builtin_macros::verus;

#[allow(unused_imports)]
use verus_builtin::*;
#[allow(unused_imports)]
use vstd::prelude::*;

#[allow(unused_imports)]
use crate::gcd::*;
#[allow(unused_imports)]
use crate::model::*;
use crate::types::{Dir, MAX_MAG, Rat};

verus! {

// ---------------------------------------------------------------------------
// The rounding specification (the mirror that the executable code is proven
// equal to)
// ---------------------------------------------------------------------------

/// The dyadic shift chosen for the value `n / d`.
///
/// `s = 62 - k`, capped at `61` so the denominator `2^s` itself stays inside
/// the budget, and floored at `0` once the value is too large to scale.
pub open spec fn snap_shift(n: int, d: int) -> nat {
    let k = bitlen(abs_int(n) / d);
    if k >= 62 {
        0nat
    } else if k == 0 {
        61nat
    } else {
        (62 - k) as nat
    }
}

/// The integer `n·2^s / d` rounded in direction `dir`.
///
/// Verus `int` division is Euclidean, which for `d > 0` is floor division.
/// Thus `a / d` is `floor(a/d)` and `-((-a) / d)` is `ceil(a/d)`. This holds
/// for negative `a` as well. `Nearest` breaks ties to an even numerator, which
/// is sign-symmetric: rounding `-x` gives the negation of rounding `x`.
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

/// Whether the *reduced* form of `n / d` satisfies I2. Equivalently, whether
/// the operation is on the exact path (R1).
pub open spec fn exact_path(n: int, d: int) -> bool {
    n == 0 || fits_budget(red_num(n, d), red_den(n, d))
}

/// The complete rounding function, in ghost form.
///
/// Every arithmetic operation `ensures` that its result is *equal to* this
/// function applied to the exact numerator and denominator. A definition as a
/// function, rather than only as a set of properties, makes commutativity and
/// cross-run determinism provable. `add(a, b)` and `add(b, a)` feed provably
/// equal `int`s into the same function.
pub open spec fn round_frac(n: int, d: int, dir: Dir) -> Rat {
    if n == 0 {
        Rat { num: 0, den: 1 }
    } else if !magnitude_fits(n, d) {
        if n > 0 {
            Rat { num: MAX_MAG, den: 1 }
        } else {
            Rat { num: (-(MAX_MAG as int)) as i64, den: 1 }
        }
    } else {
        let rn = red_num(n, d);
        let rd = red_den(n, d);
        if fits_budget(rn, rd) {
            Rat { num: rn as i64, den: rd as i64 }
        } else {
            let s = snap_shift(rn, rd);
            let sn = grid_num(rn, rd, s, dir);
            let sd = pow2(s);
            let g2 = gcd_int(sn, sd);
            Rat { num: (sn / g2) as i64, den: (sd / g2) as i64 }
        }
    }
}

/// Whether [`round_frac`] saturates. Saturation means the exact value is too
/// large in magnitude to represent at all. The `checked_*` operations return
/// `None` exactly here.
pub open spec fn saturated(n: int, d: int) -> bool {
    n != 0 && !magnitude_fits(n, d)
}

// ---------------------------------------------------------------------------
// R1 — identity on representables
// ---------------------------------------------------------------------------

/// **R1.** If the exact reduced result fits the budget, it is returned exactly.
///
/// Consequence (the exactness theorem): a computation whose exact intermediate
/// values all fit the budget is end-to-end exact. `theorem_exact_path_is_exact`
/// in [`crate::laws`] states this for whole computations.
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
        assert(round_frac(n, d, dir) == Rat { num: 0, den: 1 });
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
        // The block cannot unfold the definition of `magnitude_fits(n, d)`.
        // The inequality is therefore spelled out.
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
        assert(r == Rat { num: rn as i64, den: rd as i64 });
        // I1's zero clause: `n != 0` and `n == rn·g` force `rn != 0`. The
        // clause is thus vacuous here.
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

/// The reduction is exact: `n == red_num · g` and `d == red_den · g`.
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
/// `lemma_snap_in_budget` bounds the *snapped* pair. `round_frac` returns that
/// pair divided through by its gcd. This lemma carries the I2 bound across
/// that last step.
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
/// This lemma bridges [`crate::gcd::lemma_gcd_reduce_coprime`], which is stated
/// on `nat` magnitudes, and `gcd_int(red_num, red_den) == 1`, which invariant
/// I1 requires.
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

/// `round_frac` always produces a well-formed `Rat`. This is the V1 obligation
/// at the specification level. Proof code can thus use it without going through
/// the executable function.
///
/// The proof has four cases, one per branch: zero, saturation, the exact path,
/// and the dyadic snap. Canonicality comes from `lemma_gcd_reduce_coprime` in
/// the two reducing branches. The bounds come from `fits_budget` and
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
        // `lemma_gcd_reduce_coprime` speaks about `|n| / g`. This call
        // identifies that with `|red_num|`, which `gcd_int(rn, rd)` unfolds to.
        lemma_reduce_abs(n, d);
        lemma_reduce_magnitude_fits(n, d);
        // I1's zero clause for the exact-path arm below: `n != 0` and
        // `n == rn·g` force `rn != 0`. The clause is thus vacuous there.
        assert(rn != 0) by (nonlinear_arith)
            requires
                n != 0,
                n == rn * gcd_int(n, d),
        ;
        if fits_budget(rn, rd) {
            // `wf` reads the `i64` fields. `fits_budget` bounds the `int`s.
            assert(((rn as i64) as int) == rn);
            assert(((rd as i64) as int) == rd);
        } else {
            let s = snap_shift(rn, rd);
            let sn = grid_num(rn, rd, s, dir);
            let sd = pow2(s);
            lemma_pow2_pos(s);
            lemma_grid_error_step(rn, rd, s, dir);
            lemma_snap_magnitude(rn, rd, s, dir);
            // Coprimality of the reduced pair makes the numerator bound true
            // at the clamped shift. `lemma_gcd_reduce_coprime` above
            // establishes it.
            assert(gcd_int(rn, rd) == 1);
            lemma_snap_in_budget(rn, rd, s, sn, crate::model::bitlen(abs_int(rn) / rd));
            // The carry: `|sn|` is one past the budget exactly when the snap
            // rounds up onto `2^62`. There the reduction brings it back.
            if abs_int(sn) > max_mag() {
                lemma_carry_reduces(sn, s);
            }
            lemma_reduce_exact(sn, sd);
            lemma_gcd_reduce_coprime(abs_int(sn) as nat, sd as nat);
            lemma_reduce_abs(sn, sd);
            // I2 bounds `sn` and `sd`. The returned pair is those divided by
            // their gcd, which is no larger.
            lemma_reduce_shrinks(sn, sd);
            // The five clauses of `wf` are spelled out against the returned
            // pair. A failure thus names the clause, not the conjunction.
            let g2 = gcd_int(sn, sd);
            let on = red_num(sn, sd);
            let od = red_den(sn, sd);
            // I1's zero clause, guarded on the *reduced* numerator, which is
            // what `wf` reads. `sn == on·g2`, so a zero `on` means a zero
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
            assert(round_frac(n, d, dir) == Rat { num: on as i64, den: od as i64 });
            assert(od > 0);
            assert(abs_int(on) <= max_mag());
            assert(od <= max_mag());
            assert(on == 0 ==> od == 1);
            assert(gcd_int(on, od) == 1);
            // `wf` reads the `i64` *fields*, not the `int`s that the bounds
            // above are about. Both values are well inside the range, so the
            // casts are the identity. The clauses transfer only after that
            // fact is stated.
            crate::model::lemma_max_mag_pow2();
            assert(((on as i64) as int) == on);
            assert(((od as i64) as int) == od);
        }
    }
}

/// In the snapping branch the result's fields *are* the reduced snapped pair.
///
/// `round_frac` writes them through `as i64`. This lemma discharges that
/// round-trip, which is the purpose of `lemma_snap_in_budget`.
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
/// `lemma_grid_error_step` and `lemma_shift_covers_bound` state the bound
/// against `sn / 2^s`. `round_frac` returns that pair divided through by its
/// gcd. The inequality survives because both sides carry the factor.
pub proof fn lemma_error_after_reduce(rn: int, rd: int, sn: int, sd: int, g2: int, r: Rat)
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

/// [`lemma_error_after_reduce`] at `precision_b_nearest()` instead of
/// `precision_b()`. The proof is the same. Only the exponent changes.
pub proof fn lemma_error_after_reduce_nearest(rn: int, rd: int, sn: int, sd: int, g2: int, r: Rat)
    requires
        g2 > 0,
        r.d() > 0,
        sn == r.n() * g2,
        sd == r.d() * g2,
        abs_int(sn * rd - rn * sd) * pow2(precision_b_nearest()) <= sd * max_int(
            rd,
            abs_int(rn),
        ),
    ensures
        abs_int(r.n() * rd - rn * r.d()) * pow2(precision_b_nearest()) <= r.d() * max_int(
            rd,
            abs_int(rn),
        ),
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
    assert((e * g2) * pow2(precision_b_nearest()) == (e * pow2(precision_b_nearest())) * g2)
        by (nonlinear_arith);
    assert(sd * m == (r.d() * m) * g2) by (nonlinear_arith)
        requires
            sd == r.d() * g2,
    ;
    assert(e * pow2(precision_b_nearest()) <= r.d() * m) by (nonlinear_arith)
        requires
            g2 > 0,
            (e * pow2(precision_b_nearest())) * g2 <= (r.d() * m) * g2,
    ;
}

/// `gcd(x, 1) == 1` for every `x`. The zero and saturating branches need this,
/// because their denominators are `1`.
pub proof fn lemma_gcd_one()
    ensures
        forall|x: int| #[trigger] gcd_int(x, 1) == 1,
{
    assert forall|x: int| #[trigger] gcd_int(x, 1) == 1 by {
        crate::model::lemma_gcd_unit(x);
    }
}

/// The snapped numerator is within one of the exact scaled value. This is the
/// form that `lemma_snap_in_budget` consumes.
///
/// `|sn·rd - rn·2^s| <= rd` (one grid step) and `|rn|·2^s == q·rd + r` with
/// `0 <= r < rd` give `|sn|·rd <= q·rd + r + rd < (q + 2)·rd`. Therefore
/// `|sn| <= q + 1`.
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
    // `|sn·rd| <= |rn·2^s| + |sn·rd - rn·2^s| <= m + rd`.
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

/// **R2.** `Down` never exceeds the exact value. `Up` is never below it.
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
        // Floor and ceiling bracket the scaled value:
        // `(rn * 2^s / rd) * rd <= rn * 2^s <= ceil(...) * rd`.
        let a = rn * sd;
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(a, rd);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(-a, rd);
        assert((a / rd) * rd == rd * (a / rd)) by (nonlinear_arith);
        assert(((-a) / rd) * rd == rd * ((-a) / rd)) by (nonlinear_arith);
        assert((rn * sd) / rd * rd <= rn * sd);
        assert(rn * sd <= -(((-(rn * sd)) / rd) * rd));
        // `grid_num(.., Up) == -((-a) / rd)`. Its product with `rd` is thus
        // the negation of the product above. This step is nonlinear.
        assert((-(((-a) / rd))) * rd == -(((-a) / rd) * rd)) by (nonlinear_arith);
        lemma_grid_reduce_preserves_order(rn, rd, s, Dir::Down);
        lemma_grid_reduce_preserves_order(rn, rd, s, Dir::Up);
        // Carry the inequality from the snapped pair to the reduced one. Both
        // sides pick up the same positive factor `g2`, which then cancels.
        lemma_snap_result_fields(n, d, Dir::Down);
        lemma_snap_result_fields(n, d, Dir::Up);
        lemma_order_after_reduce(rn, rd, s, Dir::Down);
        lemma_order_after_reduce(rn, rd, s, Dir::Up);
        lemma_scale_frac_order(n, d, g, rn, rd, round_frac(n, d, Dir::Down));
        lemma_scale_frac_order(n, d, g, rn, rd, round_frac(n, d, Dir::Up));
    }
}

/// Reduction of `grid_num/2^s` by its gcd does not change the value. It
/// therefore does not change the direction of the inequality against `rn/rd`.
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
/// `Down` gives `sn·rd <= rn·2^s` and `Up` gives `sn·rd >= rn·2^s`. Division
/// of both members by `g2 == gcd(sn, 2^s)` multiplies each side of the
/// inequality by the same positive factor. The inequality thus survives.
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
pub proof fn lemma_scale_frac_order(n: int, d: int, g: int, rn: int, rd: int, r: Rat)
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

/// **R3.** `|result - exact| <= 2^-61 · max(1, |exact|)`, for every direction.
///
/// The proof is the shift analysis from the module header, carried out
/// division-free. The three cases are `k = 0` (`|x| < 1`, `s = 61`),
/// `1 <= k <= 61` (`s = 62 - k`), and `k >= 62` (`s = 0`). In each case the
/// grid step `2^-s` is below `2^-61 · max(1, |x|)`.
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
        // One grid step, scaled: `|sn·rd − rn·2^s| <= rd`. The shift bound
        // gives `rd·2^61 <= 2^s·max(rd, |rn|)`.
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

/// **R3, at `Dir::Nearest`'s tighter bound.** `|result - exact| <= 2^-62 ·
/// max(1, |exact|)`. This bound is one bit better than the uniform R3
/// statement, and specific to `Dir::Nearest`. The directed modes do not achieve
/// it. See the module header.
///
/// The shape matches [`lemma_r3_error`]. The half-step bound
/// ([`lemma_grid_error_step_nearest_half`]) replaces the whole-step bound
/// ([`lemma_grid_error_step`]), and every downstream lemma runs at
/// `precision_b_nearest()` instead of `precision_b()`.
pub proof fn lemma_r3_error_nearest(n: int, d: int)
    requires
        d > 0,
        !saturated(n, d),
    ensures
        within_error_bound_nearest(round_frac(n, d, Dir::Nearest), n, d),
{
    if exact_path(n, d) {
        lemma_r1_identity(n, d, Dir::Nearest);
        let r = round_frac(n, d, Dir::Nearest);
        assert(r.n() * d - n * r.d() == 0);
        assert(abs_int(0) == 0);
        lemma_pow2_pos(precision_b_nearest());
        assert(r.d() * max_int(d, abs_int(n)) >= 0) by (nonlinear_arith)
            requires
                r.d() > 0,
                d > 0,
        ;
        assert(within_error_bound_nearest(r, n, d));
    } else {
        lemma_reduce_exact(n, d);
        let g = gcd_int(n, d);
        let rn = red_num(n, d);
        let rd = red_den(n, d);
        let s = snap_shift(rn, rd);
        let sn = grid_num(rn, rd, s, Dir::Nearest);
        let sd = pow2(s);
        lemma_pow2_pos(s);
        lemma_pow2_pos(precision_b());
        lemma_pow2_pos(precision_b_nearest());
        lemma_grid_error_step_nearest_half(rn, rd, s);
        lemma_shift_covers_bound(rn, rd);
        lemma_round_frac_wf(n, d, Dir::Nearest);
        lemma_snap_result_fields(n, d, Dir::Nearest);
        let r = round_frac(n, d, Dir::Nearest);
        let g2 = gcd_int(sn, sd);
        crate::model::lemma_pow2_61();
        crate::model::lemma_pow2_62();
        assert(pow2(precision_b_nearest()) == 2 * pow2(precision_b()));
        // The half grid step, scaled: `2·|sn·rd − rn·2^s| <= rd`. Therefore
        // `|sn·rd − rn·2^s|·2^62 <= rd·2^61`. The direction-independent shift
        // bound gives `rd·2^61 <= 2^s·max(rd, |rn|)`.
        assert(abs_int(sn * rd - rn * sd) * pow2(precision_b_nearest()) <= rd * pow2(
            precision_b(),
        )) by (nonlinear_arith)
            requires
                2 * abs_int(sn * rd - rn * sd) <= rd,
                pow2(precision_b()) > 0,
                pow2(precision_b_nearest()) == 2 * pow2(precision_b()),
        ;
        assert(abs_int(sn * rd - rn * sd) * pow2(precision_b_nearest()) <= sd * max_int(
            rd,
            abs_int(rn),
        ));
        lemma_error_after_reduce_nearest(rn, rd, sn, sd, g2, r);
        lemma_error_scales_nearest(n, d, g, rn, rd, r, s);
        assert(within_error_bound_nearest(r, n, d));
    }
}

/// **R2 and R3 together**, at one call and under one guard.
///
/// The two lemmas share one precondition exactly: `d > 0` and
/// `!saturated(n, d)`. Every caller that needs a *value* contract, rather than
/// well-formedness alone, needs both. The ingestion constructors each state R2
/// and R3 side by side. Without this bundle each one repeats the same pair of
/// calls after the same guard. The bundle also puts a change to how the two
/// compose in one place instead of at every entry point.
pub proof fn lemma_r2_r3_directed(n: int, d: int, dir: Dir)
    requires
        d > 0,
        !saturated(n, d),
    ensures
        q_le_frac(round_frac(n, d, Dir::Down), n, d),
        q_ge_frac(round_frac(n, d, Dir::Up), n, d),
        within_error_bound(round_frac(n, d, dir), n, d),
{
    lemma_r2_directed(n, d);
    lemma_r3_error(n, d, dir);
}

/// One grid step: the snapped numerator is within `1` of the true scaled
/// value. Equivalently, `|sn·rd - rn·2^s| <= rd`.
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
            // The value is either `q` or `q + 1`. Both are within one step.
            assert(grid_num(rn, rd, s, dir) == q || grid_num(rn, rd, s, dir) == q + 1);
            assert(q * rd - a == -r);
            assert((q + 1) * rd - a == rd - r) by (nonlinear_arith)
                requires
                    a == rd * q + r,
            ;
        },
    }
}

/// The `Dir::Nearest` half step: the snapped numerator is within *half* a
/// grid step of the true scaled value. Equivalently,
/// `2·|sn·rd - rn·2^s| <= rd`.
///
/// This bound is tighter than [`lemma_grid_error_step`] by exactly the factor
/// that a round-to-nearest (ties to even) pick gains over a directed one.
/// `grid_num` picks `q` when the fractional remainder `r` is at most half of
/// `rd`, and `q + 1` when `r` is at least half. The chosen integer is thus
/// always within `rd/2`, written division-free as `2·r <= rd` or
/// `2·(rd - r) <= rd`. The tie case (`2·r == rd`) hits equality on whichever
/// side the even rule picks. That boundary carries this crate's `B = 62`
/// claim.
pub proof fn lemma_grid_error_step_nearest_half(rn: int, rd: int, s: nat)
    requires
        rd > 0,
    ensures
        2 * abs_int(grid_num(rn, rd, s, Dir::Nearest) * rd - rn * pow2(s)) <= rd,
{
    let a = rn * pow2(s);
    let q = a / rd;
    let r = a % rd;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(a, rd);
    assert(0 <= r < rd);
    let t = r * 2;
    if t > rd {
        // Rounds up: sn = q + 1 and error = rd - r. `2·r > rd` forces
        // `2·(rd - r) <= rd`.
        assert(grid_num(rn, rd, s, Dir::Nearest) == q + 1);
        assert((q + 1) * rd - a == rd - r) by (nonlinear_arith)
            requires
                a == rd * q + r,
        ;
        assert(2 * (rd - r) <= rd) by (nonlinear_arith)
            requires
                t > rd,
                t == r * 2,
        ;
    } else if t < rd {
        // Rounds down: sn = q and error = -r. `2·r < rd` gives `2·r <= rd`.
        assert(grid_num(rn, rd, s, Dir::Nearest) == q);
        assert(q * rd - a == -r);
        assert(2 * r <= rd) by (nonlinear_arith)
            requires
                t < rd,
                t == r * 2,
        ;
    } else {
        // Exact tie: both candidates sit exactly half a step away. Both
        // branches of the even rule thus land on equality.
        assert(t == rd);
        if q % 2 == 0 {
            assert(grid_num(rn, rd, s, Dir::Nearest) == q);
            assert(q * rd - a == -r);
            assert(2 * r == rd) by (nonlinear_arith)
                requires
                    t == rd,
                    t == r * 2,
            ;
        } else {
            assert(grid_num(rn, rd, s, Dir::Nearest) == q + 1);
            assert((q + 1) * rd - a == rd - r) by (nonlinear_arith)
                requires
                    a == rd * q + r,
            ;
            assert(2 * (rd - r) == rd) by (nonlinear_arith)
                requires
                    t == rd,
                    t == r * 2,
            ;
        }
    }
}

/// The shift is large enough for R3: `rd · 2^61 <= 2^s · max(rd, |rn|)`.
///
/// This lemma is the core of the bound. `k = bitlen(|rn|/rd)` gives
/// `|rn| >= 2^(k-1) · rd` whenever `k >= 1`, and `s = 62 - k`. Therefore
/// `2^s · |rn| >= 2^(62-k) · 2^(k-1) · rd = 2^61 · rd`. For `k = 0` the shift
/// caps at `61`, and `max(rd, |rn|) >= rd` suffices.
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
    // These calls must be in the *enclosing* context. A `nonlinear_arith`
    // block sees only its own `requires`, thus facts from a nested `by` block
    // never reach one.
    lemma_pow2_pos(61nat);
    lemma_pow2_pos(62nat);
    lemma_pow2_pos(s);
    if k == 0 {
        assert(s == 61);
        assert(max_int(rd, abs_int(rn)) >= rd);
        assert(rd * pow2(61) <= pow2(61) * max_int(rd, abs_int(rn))) by (nonlinear_arith)
            requires
                pow2(61) > 0,
                rd <= max_int(rd, abs_int(rn)),
        ;
    } else {
        // `|rn| >= ip * rd >= 2^(k-1) * rd`.
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
        if k >= 62 {
            assert(s == 0 && pow2(s) == 1);
            lemma_pow2_mono(61nat, (k - 1) as nat);
            assert(rd * pow2(61) <= pow2((k - 1) as nat) * rd) by (nonlinear_arith)
                requires
                    rd > 0,
                    pow2(61) <= pow2((k - 1) as nat),
            ;
            assert(pow2((k - 1) as nat) * rd <= max_int(rd, abs_int(rn)));
            assert(pow2(s) * max_int(rd, abs_int(rn)) == max_int(rd, abs_int(rn)))
                by (nonlinear_arith)
                requires
                    pow2(s) == 1,
            ;
        } else {
            assert(s == 62 - k);
            crate::model::lemma_pow2_add(s, (k - 1) as nat);
            assert(s + (k - 1) == 61);
            assert(pow2(s) * pow2((k - 1) as nat) == pow2(61));
            assert(rd * pow2(61) <= pow2(s) * abs_int(rn)) by (nonlinear_arith)
                requires
                    rd > 0,
                    pow2(s) > 0,
                    abs_int(rn) >= pow2((k - 1) as nat) * rd,
                    pow2(s) * pow2((k - 1) as nat) == pow2(61),
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

/// Combines the grid step, the shift bound, and the gcd re-reduction into the
/// division-free R3 statement against the *unreduced* `n / d`.
pub proof fn lemma_error_scales(n: int, d: int, g: int, rn: int, rd: int, r: Rat, s: nat)
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

/// [`lemma_error_scales`] at `precision_b_nearest()` instead of
/// `precision_b()`. The proof is the same. Only the exponent and the target
/// predicate change. The target predicate is `within_error_bound_nearest`
/// instead of `within_error_bound`.
pub proof fn lemma_error_scales_nearest(n: int, d: int, g: int, rn: int, rd: int, r: Rat, s: nat)
    requires
        g > 0,
        rd > 0,
        n == rn * g,
        d == rd * g,
        r.d() > 0,
        abs_int(r.n() * rd - rn * r.d()) * pow2(precision_b_nearest()) <= r.d() * max_int(
            rd,
            abs_int(rn),
        ),
    ensures
        within_error_bound_nearest(r, n, d),
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
    assert(within_error_bound_nearest(r, n, d)) by (nonlinear_arith)
        requires
            g > 0,
            r.n() * d - n * r.d() == (r.n() * rd - rn * r.d()) * g,
            max_int(d, abs_int(n)) == max_int(rd, abs_int(rn)) * g,
            abs_int((r.n() * rd - rn * r.d()) * g) == abs_int(r.n() * rd - rn * r.d()) * g,
            abs_int(r.n() * rd - rn * r.d()) * pow2(precision_b_nearest()) <= r.d() * max_int(
                rd,
                abs_int(rn),
            ),
    ;
}

// ---------------------------------------------------------------------------
// R4 — monotonicity (stated per grid, as the specification permits)
// ---------------------------------------------------------------------------

/// **R4.** On a fixed grid `2^-s`, the snap is monotone. If `n1/d1 <= n2/d2`
/// then the snapped numerators are ordered the same way, in every direction.
///
/// The statement is per-grid. The *composed* operation ("return exactly if it
/// fits, otherwise snap") is **not** globally monotone. See the counterexample
/// in `README.md`. This crate does not claim global monotonicity.
pub proof fn lemma_r4_monotone_grid(n1: int, d1: int, n2: int, d2: int, s: nat, dir: Dir)
    requires
        d1 > 0,
        d2 > 0,
        n1 * d2 <= n2 * d1,
    ensures
        grid_num(n1, d1, s, dir) * d2 * d1 <= grid_num(n2, d2, s, dir) * d1 * d2,
{
    lemma_pow2_pos(s);
    // The scaled values are ordered: `(n1·2^s)/d1 <= (n2·2^s)/d2`.
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
    // real value. `a1/d1 <= a2/d2`, thus the rounded integers are ordered.
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(a1, d1);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(a2, d2);
    let q1 = round_int(a1, d1, dir);
    let q2 = round_int(a2, d2, dir);
    match dir {
        Dir::Down => {
            lemma_floor_div_monotone(a1, d1, a2, d2);
        },
        Dir::Up => {
            // Ceiling is the negation of the floor of the negation. The
            // negation also flips the hypothesis.
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
            // rounded value lies in {floor, floor + 1}. When the floors agree,
            // the fractional parts are ordered, and the tie rule is monotone
            // in them. Both `2r > d` and `2r == d` propagate upwards.
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

/// The direction-independent kernel that [`grid_num`] uses. It is a separate
/// item so that monotonicity has a single statement.
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
    // `q1 <= a1/d1 <= a2/d2 < q2 + 1`, therefore `q1 <= q2`.
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

/// `gcd(|m|, 2^s)`, without a gcd.
///
/// The second reduction of the snap path always takes its gcd against `2^s`,
/// and the answer to that is `2^min(v2(m), s)`: strip the twos that `m` and
/// `2^s` share and stop at whichever runs out first. This loop does that in at
/// most `s` halvings of an `i128`, where each halving is a shift. The general
/// gcd it replaces runs Euclid's narrowing step and then the binary loop.
///
/// `crate::gcd::lemma_gcd_odd_pow2` closes the exit case: when `m` has no more
/// twos, what remains is odd, and an odd number is coprime to a power of two.
pub fn gcd_pow2_i128(m: i128, s: u32) -> (r: i128)
    requires
        s <= 61,
        abs_int(m as int) < pow2(126),
    ensures
        r as int == crate::model::gcd_int(m as int, pow2(s as nat)),
        r > 0,
{
    proof {
        crate::model::lemma_pow2_124();
        crate::model::lemma_pow2_126();
        lemma_pow2_pos(s as nat);
    }
    let mut q: i128 = if m < 0 {
        0 - m
    } else {
        m
    };
    let mut g: i128 = 1;
    let mut e: u32 = 0;
    proof {
        // `g == 1 <= 2^61` before the first iteration.
        lemma_pow2_pos(61nat);
    }
    while e < s && q % 2 == 0
        invariant
            e <= s,
            s <= 61,
            g == pow2(e as nat),
            g > 0,
            q >= 0,
            (q as int) * (g as int) == abs_int(m as int),
            crate::model::gcd_int(m as int, pow2(s as nat)) == (g as int) * crate::model::gcd_nat(
                q as nat,
                pow2((s - e) as nat) as nat,
            ),
            g <= pow2(61nat),
        decreases s - e,
    {
        proof {
            // Both sides are even here, thus one common factor of two comes
            // out of the gcd.
            lemma_pow2_pos((s - e) as nat);
            assert(pow2((s - e) as nat) == 2 * pow2((s - e - 1) as nat));
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
                pow2((s - e) as nat),
                2int,
                pow2((s - e - 1) as nat),
                0int,
            );
            crate::gcd::lemma_gcd_both_even(q as nat, pow2((s - e) as nat) as nat);
            // `g` doubles and `q` halves, thus their product is unchanged.
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(q as int, 2int);
            assert((q as int) / 2 * ((g as int) * 2) == (q as int) * (g as int))
                by (nonlinear_arith)
                requires
                    (q as int) == 2 * ((q as int) / 2),
            ;
            assert(pow2((e + 1) as nat) == 2 * pow2(e as nat));
            lemma_pow2_mono((e + 1) as nat, 61nat);
            // The doubling needs a literal bound to discharge its `i128` range
            // check. `2^61 <= 2^125`, and `2^125` has one.
            lemma_pow2_mono(61nat, 125nat);
            crate::model::lemma_pow2_125();
            // Move the factor of two from the gcd onto `g`:
            // `(2g)·x == g·(2x)`, at the value the invariant carries.
            let x = crate::model::gcd_nat(
                ((q as int) / 2) as nat,
                pow2((s - e - 1) as nat) as nat,
            ) as int;
            assert(((g as int) * 2) * x == (g as int) * (2 * x)) by (nonlinear_arith);
        }
        q = q / 2;
        g = g * 2;
        e = e + 1;
    }
    proof {
        // The loop ends either with the twos of `2^s` exhausted, or with `q`
        // odd. Both leave a gcd of one.
        if e == s {
            assert(pow2(0nat) == 1);
            crate::gcd::lemma_gcd_odd_pow2(1nat, 0nat);
            assert(crate::model::gcd_nat(q as nat, 1nat) == 1) by {
                assert((q as nat) % 1 == 0);
            }
        } else {
            assert(q % 2 != 0);
            assert((q as nat) % 2 == 1);
            crate::gcd::lemma_gcd_odd_pow2(q as nat, (s - e) as nat);
        }
    }
    g
}

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
            // The literal discharges the `i128` overflow check on `p * 2`.
            // `p <= pow2(126)` alone tells the solver nothing about the
            // machine type.
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
            // A literal, for the same reason as in `pow2_i128`. Inside the
            // loop `p <= x < 2^126`, thus `p * 2 < 2^127` and the doubling is
            // safe.
            x <= 85070591730234615865843651857942052864,
            forall|j: nat| j < k as nat ==> pow2(j) <= x,
        // `x - p` is not a legal measure. It is non-negative only while the
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

/// `2^(k-1) <= x < 2^k` characterises `bitlen`. Any `k` with that property is
/// therefore *the* bit length.
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
/// `n · 2^s`**. That product overflows `i128` for the denominators this crate
/// handles.
///
/// The loop carries `q`, bounded by `2^62` through the precondition, and
/// `rem`, bounded by `d`. The widest live value is therefore
/// `2 · rem < 2 · 2^124 = 2^125`.
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
            // `rem * 2 < 2^125` safe, and `q < 2^62` makes `q * 2 + 1` safe.
            // In `pow2` form they discharge neither check.
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
            // Doubling the carried identity. `(2q)·d == 2·(q·d)` is nonlinear.
            // Outside a nonlinear block the two sides are unrelated terms.
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

/// The bound that every caller must respect on the numerator given to
/// [`round_frac_exec`]: `2^126`. All of this crate's intermediates are below
/// `2^125`.
pub open spec fn num_input_bound() -> int {
    pow2(126)
}

/// The bound that every caller must respect on the denominator: `2^124`.
pub open spec fn den_input_bound() -> int {
    pow2(124)
}

/// Canonicalise (and, if necessary, round) the exact fraction `n / d`.
///
/// This function is the single place where an exact `i128` intermediate
/// becomes a `Rat`. Every arithmetic operation in [`crate::q`] ends here.
pub fn round_frac_exec(n: i128, d: i128, dir: Dir) -> (r: Rat)
    requires
        d > 0,
        abs_int(n as int) < num_input_bound(),
        d as int <= den_input_bound(),
    ensures
        r.wf(),
        r == round_frac(n as int, d as int, dir),
{
    proof {
        // `gcd_abs_i128` bounds its numerator by a literal, and the input bound
        // here is stated with `pow2`. The literal has to be concretised first.
        crate::model::lemma_pow2_126();
    }
    let g: i128 = gcd_abs_i128(n, d);
    round_frac_exec_with_gcd(n, d, g, dir)
}

/// [`round_frac_exec`], with the gcd supplied by the caller.
///
/// The gcd is the dominant cost of an arithmetic operation, and at `i128` width
/// it is the most expensive form of it. A caller that already knows the gcd of
/// its own pair can skip that work. `Rat::mul_dir` and `Rat::div_dir` know it:
/// by `lemma_gcd_cross`, the gcd of a product of two canonical fractions is the
/// product of two gcds taken across the operands, and those operands are
/// bounded by `MAX_MAG`, thus each of those two gcds is a `u64` gcd.
///
/// The precondition pins `g` to the same value the general entry point would
/// compute, thus the postcondition is identical and no caller can pass a
/// number that changes the result.
pub fn round_frac_exec_with_gcd(n: i128, d: i128, g: i128, dir: Dir) -> (r: Rat)
    requires
        d > 0,
        abs_int(n as int) < num_input_bound(),
        d as int <= den_input_bound(),
        g as int == crate::model::gcd_int(n as int, d as int),
    ensures
        r.wf(),
        r == round_frac(n as int, d as int, dir),
{
    proof {
        lemma_gcd_int_facts(n as int, d as int);
        // The input bounds use `pow2`, which discharges no `i128` overflow or
        // range check on its own. The two literals thus come first.
        crate::model::lemma_pow2_124();
        crate::model::lemma_pow2_126();
        crate::model::lemma_max_mag_pow2();
        // Every branch that returns a denominator of one needs this. Those
        // branches are the zero case and both saturating cases.
        lemma_gcd_one();
        lemma_round_frac_wf(n as int, d as int, dir);
    }
    if n == 0 {
        return Rat { num: 0, den: 1 };
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
            return Rat { num: MAX_MAG, den: 1 };
        } else {
            return Rat { num: -MAX_MAG, den: 1 };
        }
    }
    proof {
        lemma_magnitude_test(m0 as int, d as int, ip0 as int, fr0 as int);
    }
    proof {
        // `red_den > 0`, therefore `g <= d`, therefore the divisions below are
        // safe. The two exactness equations are `n == rn·g` and `d == rd·g`.
        lemma_reduce_exact(n as int, d as int);
        lemma_gcd_reduce_coprime(abs_int(n as int) as nat, d as nat);
        lemma_reduce_abs(n as int, d as int);
        lemma_reduce_magnitude_fits(n as int, d as int);
        // The reduction equations have the form `x == r·g`. The quotient lemma
        // needs `g·r`. Outside a nonlinear block those are distinct terms.
        assert((g as int) * red_num(n as int, d as int) == red_num(n as int, d as int) * (
        g as int)) by (nonlinear_arith);
        assert((g as int) * red_den(n as int, d as int) == red_den(n as int, d as int) * (
        g as int)) by (nonlinear_arith);
        assert((g as int) * abs_int(red_num(n as int, d as int)) == abs_int(
            red_num(n as int, d as int),
        ) * (g as int)) by (nonlinear_arith);
        // I1's zero clause on the exact-path return below: `n != 0` and
        // `n == rn·g` force `rn != 0`. The clause is thus vacuous.
        assert(red_num(n as int, d as int) != 0) by (nonlinear_arith)
            requires
                n != 0,
                (n as int) == red_num(n as int, d as int) * (g as int),
        ;
    }
    // A coprime pair is the common case for small operands, and `x / 1` is
    // still an `i128` division, which is a call into `compiler_builtins`. Both
    // arms establish the same two facts, so the proof below sees no case split.
    let rn: i128;
    let rd: i128;
    if g == 1 {
        proof {
            vstd::arithmetic::div_mod::lemma_div_basics(n as int);
            vstd::arithmetic::div_mod::lemma_div_basics(d as int);
        }
        rn = n;
        rd = d;
    } else {
        rn = n / g;
        rd = d / g;
    }
    proof {
        assert(rn as int == red_num(n as int, d as int));
        assert(rd as int == red_den(n as int, d as int));
    }
    let arn: i128 = if rn < 0 {
        0 - rn
    } else {
        rn
    };
    if arn <= mm && rd <= mm {
        return Rat { num: rn as i64, den: rd as i64 };
    }
    // --- dyadic snap -------------------------------------------------------
    proof {
        vstd::arithmetic::div_mod::lemma_div_pos_is_pos(arn as int, rd as int);
    }
    let ip: i128 = arn / rd;
    let k: u32 = bitlen_i128(ip);
    let s: u32 = if k >= 62 {
        0
    } else if k == 0 {
        61
    } else {
        62 - k
    };
    proof {
        // The overflow test above bounds `|n| / d`. The shift comes from
        // `arn / rd`. Reduction does not move the integer part, thus the bound
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
        // `lemma_snap_in_budget` needs the one-grid-step bound on `|sn|`,
        // which is the conclusion of `lemma_snap_magnitude`.
        lemma_snap_magnitude(rn as int, rd as int, s as nat, dir);
        lemma_snap_in_budget(rn as int, rd as int, s as nat, sn as int, k as nat);
    }
    // The gcd against `2^s` needs no gcd: it is the common power of two.
    let g2: i128 = gcd_pow2_i128(sn, s);
    let on: i128 = sn / g2;
    let od: i128 = sd / g2;
    proof {
        lemma_reduce_exact(sn as int, sd as int);
        lemma_gcd_reduce_coprime(abs_int(sn as int) as nat, sd as nat);
        lemma_reduce_abs(sn as int, sd as int);
        // I2 holds of `sn` and `sd`. The returned pair is those divided by
        // their gcd, which is no larger.
        lemma_reduce_shrinks(sn as int, sd as int);
        // I1's zero clause, guarded on the reduced numerator. That is the
        // field `wf` reads. Even `0 · g2` is an uninterpreted product here.
        if on == 0 {
            assert(sn as int == 0) by (nonlinear_arith)
                requires
                    sn as int == (on as int) * (g2 as int),
                    on as int == 0,
            ;
            crate::gcd::lemma_gcd_zero(sd as nat);
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
                sd as int,
                sd as int,
                1,
                0,
            );
        }
        crate::model::lemma_max_mag_pow2();
        assert(((on as i64) as int) == on as int);
        assert(((od as i64) as int) == od as int);
    }
    Rat { num: on as i64, den: od as i64 }
}

/// `|n| <= MAX_MAG · d` is exactly `ip < MAX_MAG || (ip == MAX_MAG && fr == 0)`
/// for `ip = |n| / d` and `fr = |n| % d`. This form is the overflow test
/// without ever forming `MAX_MAG · d`, which overflows `i128`.
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
    // The two implications above leave the boundary case `ip == max_mag()`
    // open. There `m == max_mag()·d + fr`, thus `m <= max_mag()·d` holds
    // exactly when `fr == 0`. Z3 needs only the commuted product to see it.
    assert(d * ip == ip * d) by (nonlinear_arith);
}

/// Reducing a fraction by a common divisor leaves its integer part alone:
/// `(g·rm) / (g·rd) == rm / rd`.
///
/// The overflow test in [`round_frac_exec`] runs on the *unreduced* pair. The
/// shift comes from the *reduced* pair. This lemma lets the first bound travel
/// to the second.
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
    // `m == d·q + g·r` with `0 <= g·r < g·rd == d`. This pins `m / d` to `q`.
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
/// unreduced pair. Both then give the reduced pair to `lemma_snap_in_budget`.
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

/// The `shift_div` precondition holds for the shift that the algorithm picks.
pub proof fn lemma_shift_div_precondition(m: int, rd: int, s: nat, k: nat)
    requires
        rd > 0,
        m >= 0,
        k == bitlen(m / rd),
        s == (if k >= 62 { 0nat } else if k == 0 { 61nat } else { (62 - k) as nat }),
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
    if k >= 62 {
        assert(s == 0 && pow2(s) == 1);
        // `ip <= max_mag()` is a hypothesis, and `max_mag() == 2^62 - 1`. The
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
        // `s + k` is `61` at the capped shift (`k == 0`) and `62` otherwise.
        // Both branches land at or under the `2^62` that the caller needs.
        let b: nat = if k == 0 {
            61nat
        } else {
            62nat
        };
        assert(ip < pow2(k));
        assert(ip + 1 <= pow2(k));
        crate::model::lemma_pow2_add(s, k);
        assert(s + k == b);
        assert(pow2(s) * pow2(k) == pow2(b));
        lemma_pow2_pos(s);
        lemma_pow2_pos(k);
        assert(m * pow2(s) < rd * pow2(b)) by (nonlinear_arith)
            requires
                rd > 0,
                pow2(s) > 0,
                m < (ip + 1) * rd,
                ip + 1 <= pow2(k),
                pow2(s) * pow2(k) == pow2(b),
        ;
        assert(pow2(b) <= pow2(62)) by {
            lemma_pow2_mono(b, 62nat);
        }
        assert(rd * pow2(b) <= rd * pow2(62)) by (nonlinear_arith)
            requires
                rd > 0,
                pow2(b) <= pow2(62),
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
    // Outside a `nonlinear_arith` block multiplication is uninterpreted. Thus
    // `qf * rd` and `rd * qf` are different terms to the solver, and
    // `lemma_fundamental_div_mod_converse` needs the divisor first.
    assert(rd * qf == qf * rd) by (nonlinear_arith);
    if rn >= 0 {
        assert(a == abs_int(rn) * pow2(s));
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(a, rd, qf, rf);
        assert(a / rd == qf && a % rd == rf);
        // The specification of `Up` is `-((-a) / rd)`. The negated quotient is
        // therefore needed here too. It is `-qf` at an exact division and
        // `-(qf + 1)` otherwise.
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
        // its own `requires`. Its definition is therefore restated here.
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
            // `Nearest`'s tie rule uses the parity of the *floor*. For a
            // negative value the floor is `-(qf + 1)`, which has the opposite
            // parity to `qf`. That flip is why the specification's tie test
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

/// The carry case: the snapped numerator lands exactly on `2^62`, one past the
/// budget.
///
/// The carry is the price of a shift that spends the whole budget on the
/// scaled numerator instead of reserving a bit of headroom. This lemma handles
/// the case rather than avoiding it by construction. The case costs nothing,
/// because the pair is `±2^62 / 2^s` with `s >= 1`. `2^s` divides `2^62`, thus
/// the reduction is `±2^(62-s) / 1`. `62 - s <= 61` puts that comfortably
/// inside I2.
pub proof fn lemma_carry_reduces(sn: int, s: nat)
    requires
        abs_int(sn) == pow2(62),
        1 <= s <= 61,
    ensures
        fits_budget(red_num(sn, pow2(s)), red_den(sn, pow2(s))),
{
    crate::model::lemma_max_mag_pow2();
    lemma_pow2_pos(s);
    lemma_pow2_pos((62 - s) as nat);
    crate::model::lemma_pow2_add(s, (62 - s) as nat);
    assert(pow2(s) * pow2((62 - s) as nat) == pow2(62));
    let p = pow2(s);
    let t = pow2((62 - s) as nat);
    let g = gcd_int(sn, p);
    // `2^s` is a common divisor of `|sn| == 2^62` and of `2^s`. It therefore
    // divides the gcd. The gcd divides `2^s`. Both are positive, thus the two
    // are equal.
    assert(divides(p, abs_int(sn))) by {
        assert(abs_int(sn) == p * t);
    }
    assert(divides(p, p)) by {
        assert(p == p * 1);
    }
    lemma_gcd_greatest(abs_int(sn) as nat, p as nat, p);
    lemma_gcd_pos(abs_int(sn) as nat, p as nat);
    lemma_gcd_le(abs_int(sn) as nat, p as nat);
    crate::model::lemma_divides_le(p, g);
    assert(g == p);
    // `|sn| / 2^s == 2^(62-s) <= 2^61 <= MAX_MAG`. The denominator is 1.
    lemma_pow2_mono((62 - s) as nat, 61nat);
    assert(abs_int(red_num(sn, p)) == t) by {
        if sn > 0 {
            assert(sn == p * t);
            vstd::arithmetic::div_mod::lemma_div_multiples_vanish(t, p);
        } else {
            assert(sn == -(p * t));
            assert(sn == p * (-t)) by (nonlinear_arith)
                requires
                    sn == -(p * t),
            ;
            vstd::arithmetic::div_mod::lemma_div_multiples_vanish(-t, p);
        }
    }
    assert(red_den(sn, p) == 1) by {
        vstd::arithmetic::div_mod::lemma_div_multiples_vanish(1, p);
        assert(p * 1 == p);
    }
}

/// The snapped denominator fits the budget, and the numerator does too except
/// in the single carry case handled by [`lemma_carry_reduces`].
///
/// Denominator: `2^s <= 2^61 <= MAX_MAG`.
///
/// Numerator, for `k == 0` (`|x| < 1`, shift capped at `61`): the snapped
/// quotient is below `2^61`, and one more than it still fits.
///
/// Numerator, for `1 <= k <= 61`: `s = 62 - k` and `|rn| < 2^k·rd`, thus the
/// quotient is below `2^62`. Rounding up can therefore land on `2^62` exactly,
/// one past the budget. That case is the carry.
///
/// Numerator, for `k >= 62` (shift clamped to `0`): the result is `ceil(|x|)`,
/// thus `floor(|x|) < MAX_MAG` suffices. Equality gives `|rn| == MAX_MAG·rd`
/// exactly, thus `rd` divides `|rn|`. Coprimality then forces `rd == 1`, and
/// `|rn| == MAX_MAG` means the pair fits the budget. That contradicts the
/// hypothesis that it does not. Coprimality is therefore a precondition here:
/// without it the bound is false.
pub proof fn lemma_snap_in_budget(rn: int, rd: int, s: nat, sn: int, k: nat)
    requires
        rd > 0,
        rn != 0,
        gcd_int(rn, rd) == 1,
        abs_int(rn) <= max_mag() * rd,
        !fits_budget(rn, rd),
        k == bitlen(abs_int(rn) / rd),
        s == (if k >= 62 { 0nat } else if k == 0 { 61nat } else { (62 - k) as nat }),
        abs_int(sn) <= abs_int(rn) * pow2(s) / rd + 1,
    ensures
        abs_int(sn) <= max_mag() || (abs_int(sn) == pow2(62) && 1 <= s <= 61),
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
    if k >= 62 {
        assert(s == 0 && pow2(s) == 1);
        assert(m == abs_int(rn));
        assert(q == ip);
        // The magnitude hypothesis gives `ip <= max_mag()`.
        assert(ip <= max_mag()) by (nonlinear_arith)
            requires
                rd > 0,
                abs_int(rn) <= max_mag() * rd,
                abs_int(rn) == rd * ip + abs_int(rn) % rd,
                abs_int(rn) % rd >= 0,
        ;
        // Strictness: equality makes `rd` divide `|rn|`.
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
        // `s + k` is `61` at the capped shift (`k == 0`), where no carry is
        // possible. It is `62` otherwise. At `62` rounding up can land exactly
        // on `2^62`. That is the carry that the postcondition's disjunct
        // admits.
        let b: nat = if k == 0 {
            61nat
        } else {
            62nat
        };
        assert(s + k == b);
        crate::model::lemma_pow2_add(s, k);
        assert(pow2(s) * pow2(k) == pow2(b));
        lemma_pow2_pos(k);
        // `|rn| < (ip + 1)·rd <= 2^k·rd`.
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
        // `q·rd <= m == |rn|·2^s < 2^k·rd·2^s == 2^b·rd`, thus `q < 2^b`.
        assert(q * rd <= m) by (nonlinear_arith)
            requires
                m == rd * q + m % rd,
                m % rd >= 0,
        ;
        assert(m < pow2(b) * rd) by (nonlinear_arith)
            requires
                rd > 0,
                pow2(s) > 0,
                m == abs_int(rn) * pow2(s),
                abs_int(rn) < pow2(k) * rd,
                pow2(s) * pow2(k) == pow2(b),
        ;
        assert(q < pow2(b)) by (nonlinear_arith)
            requires
                rd > 0,
                q * rd <= m,
                m < pow2(b) * rd,
        ;
        // `|sn| <= q + 1 <= 2^b`. At `b == 61` that value is inside the
        // budget. At `b == 62` it is inside the budget or exactly the carry
        // value.
        if k == 0 {
            crate::model::lemma_max_mag_pow2();
            lemma_pow2_mono(61nat, 62nat);
        }
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
    // `divides(rd, rd)` is a precondition of `lemma_gcd_greatest`. It must
    // therefore be in scope *before* the call, not after it.
    crate::model::lemma_divides_basic(rd);
    crate::gcd::lemma_gcd_greatest(abs_int(rn) as nat, rd as nat, rd);
    crate::model::lemma_divides_le(rd, 1);
}

// ---------------------------------------------------------------------------
// Below the finest grid
// ---------------------------------------------------------------------------

/// `2^61`, the denominator of the finest dyadic grid this crate rounds onto.
pub open spec fn finest_grid_den() -> int {
    pow2(61)
}

/// Where a nonzero value strictly inside the first grid cell lands.
///
/// `Nearest` collapses the value to zero. The directed modes must stay on
/// their own side of it, thus they return the neighbouring grid point.
///
/// The denominator goes through [`finest_grid_den`] rather than a repeated
/// literal. This ties the definition to `pow2(61)` instead of to a digit
/// string that needs a manual check against the one in `convert::tiny`.
pub open spec fn subgrid_endpoint(positive: bool, dir: Dir) -> Rat {
    match dir {
        Dir::Nearest => Rat { num: 0, den: 1 },
        Dir::Down => if positive {
            Rat { num: 0, den: 1 }
        } else {
            Rat { num: (-1int) as i64, den: finest_grid_den() as i64 }
        },
        Dir::Up => if positive {
            Rat { num: 1, den: finest_grid_den() as i64 }
        } else {
            Rat { num: 0, den: 1 }
        },
    }
}

/// **Rounding below the finest grid.** A nonzero value whose magnitude is
/// under `2^-62` lies strictly inside half the first dyadic cell. It rounds to
/// that cell's endpoint on the correct side.
///
/// `convert::tiny` computes this endpoint directly. It is the one input path
/// whose denominator (`2^s` for `s > 124`) exceeds what `round_frac_exec`
/// accepts. The executable code therefore cannot call the rounder and inherit
/// its contract. A proof that the shortcut *equals* `round_frac` lets
/// `from_parts_dir` state one uniform postcondition over all its branches,
/// instead of an exception that nobody then reasons about.
#[verifier::rlimit(40)]
pub proof fn lemma_round_frac_subgrid(n: int, d: int, dir: Dir)
    requires
        d > 0,
        n != 0,
        abs_int(n) * pow2(62) < d,
    ensures
        round_frac(n, d, dir) == subgrid_endpoint(n > 0, dir),
        // This clause is public rather than private. The proof below must
        // establish it anyway to reach `round_frac`, and the one caller needs
        // exactly this to discharge R2/R3's `!saturated` guard. An internal
        // form makes the caller repeat the identical `nonlinear_arith` block.
        magnitude_fits(n, d),
{
    lemma_pow2_pos(61nat);
    lemma_pow2_pos(62nat);
    lemma_pow2_61();
    lemma_pow2_62();
    lemma_max_mag_pow2();

    let g = gcd_int(n, d);
    let rn = red_num(n, d);
    let rd = red_den(n, d);
    lemma_reduce_exact(n, d);
    lemma_reduce_abs(n, d);

    // The hypothesis survives reduction. Both sides carry a factor of `g`.
    assert(abs_int(rn) >= 1) by (nonlinear_arith)
        requires
            abs_int(n) == abs_int(rn) * g,
            abs_int(n) >= 1,
            g > 0,
    ;
    assert(abs_int(rn) * pow2(62) < rd) by (nonlinear_arith)
        requires
            abs_int(n) * pow2(62) < d,
            abs_int(n) == abs_int(rn) * g,
            d == rd * g,
            g > 0,
    ;

    // Not saturated: the value is tiny, thus it fits.
    assert(abs_int(n) <= max_mag() * d) by (nonlinear_arith)
        requires
            abs_int(n) * pow2(62) < d,
            abs_int(n) >= 1,
            pow2(62) >= 1,
            max_mag() >= 1,
            d > 0,
    ;
    assert(magnitude_fits(n, d));

    // The reduced pair still does not fit the budget. `|rn| >= 1` forces
    // `rd > 2^62`, one past the ceiling.
    assert(rd > max_mag()) by (nonlinear_arith)
        requires
            abs_int(rn) * pow2(62) < rd,
            abs_int(rn) >= 1,
            max_mag() == pow2(62) - 1,
    ;
    assert(!fits_budget(rn, rd));

    // The value therefore snaps, and onto the *finest* grid. Its integer part
    // is zero, `bitlen(0) == 0`, and `snap_shift` sends that to 61.
    assert(abs_int(rn) < rd) by (nonlinear_arith)
        requires
            abs_int(rn) * pow2(62) < rd,
            abs_int(rn) >= 0,
            pow2(62) >= 1,
    ;
    assert(abs_int(rn) / rd == 0) by {
        vstd::arithmetic::div_mod::lemma_basic_div_specific_divisor(rd);
    }
    assert(bitlen(abs_int(rn) / rd) == 0);
    let s = snap_shift(rn, rd);
    assert(s == 61nat);

    let a = rn * pow2(61);
    assert(abs_int(a) == abs_int(rn) * pow2(61)) by {
        lemma_abs_mul_pos(rn, pow2(61));
    }
    // Half a cell: `2·|a| < rd`. Every direction below needs this bound.
    assert(2 * abs_int(a) < rd) by (nonlinear_arith)
        requires
            abs_int(a) == abs_int(rn) * pow2(61),
            abs_int(rn) * pow2(62) < rd,
            pow2(62) == 2 * pow2(61),
    ;
    assert(a != 0) by (nonlinear_arith)
        requires
            abs_int(a) == abs_int(rn) * pow2(61),
            abs_int(rn) >= 1,
            pow2(61) >= 1,
    ;
    assert((a > 0) == (rn > 0)) by (nonlinear_arith)
        requires
            a == rn * pow2(61),
            pow2(61) > 0,
    ;
    assert((rn > 0) == (n > 0)) by (nonlinear_arith)
        requires
            n == rn * g,
            g > 0,
    ;

    let sn = grid_num(rn, rd, s, dir);
    lemma_subgrid_grid_num(a, rd, dir);
    assert(sn == if a > 0 {
        match dir {
            Dir::Down => 0int,
            Dir::Up => 1int,
            Dir::Nearest => 0int,
        }
    } else {
        match dir {
            Dir::Down => -1int,
            Dir::Up => 0int,
            Dir::Nearest => 0int,
        }
    });

    // Finally, reduce the snapped pair. `gcd(0, 2^61) == 2^61` collapses the
    // zero case to `0/1`. `gcd(±1, 2^61) == 1` leaves the endpoints alone.
    let sd = pow2(61);
    if sn == 0 {
        assert(gcd_int(0, sd) == sd) by {
            crate::gcd::lemma_gcd_zero(sd as nat);
        }
        assert(sd / sd == 1) by (nonlinear_arith)
            requires
                sd > 0,
        ;
    } else {
        assert(abs_int(sn) == 1);
        assert(gcd_int(sn, sd) == 1) by {
            crate::gcd::lemma_gcd_pos(abs_int(sn) as nat, sd as nat);
            crate::gcd::lemma_gcd_le(abs_int(sn) as nat, sd as nat);
        }
    }
}

/// The three directions at a value strictly inside half the first grid cell.
///
/// This lemma is separate because it is pure Euclidean-division case analysis
/// on `a` and `rd`. It uses no rationals and no reduction. Inside the caller it
/// forms a single goal that the solver does not take whole.
pub proof fn lemma_subgrid_grid_num(a: int, rd: int, dir: Dir)
    requires
        rd > 0,
        a != 0,
        2 * abs_int(a) < rd,
    ensures
        (dir == Dir::Down && a > 0) ==> a / rd == 0,
        (dir == Dir::Down && a < 0) ==> a / rd == -1,
        (dir == Dir::Up && a > 0) ==> -((-a) / rd) == 1,
        (dir == Dir::Up && a < 0) ==> -((-a) / rd) == 0,
        a / rd == (if a > 0 {
            0int
        } else {
            -1int
        }),
        a % rd == (if a > 0 {
            a
        } else {
            a + rd
        }),
{
    if a > 0 {
        assert(0 <= a < rd) by (nonlinear_arith)
            requires
                2 * abs_int(a) < rd,
                a > 0,
                abs_int(a) == a,
        ;
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(a, rd, 0, a);
        assert((-a) / rd == -1) by {
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(-a, rd, -1, rd - a);
        }
    } else {
        assert(0 < -a < rd) by (nonlinear_arith)
            requires
                2 * abs_int(a) < rd,
                a < 0,
                abs_int(a) == -a,
        ;
        assert(a / rd == -1) by {
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(a, rd, -1, rd + a);
        }
        assert(a % rd == a + rd) by {
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(a, rd, -1, rd + a);
        }
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(-a, rd, 0, -a);
    }
}

} // verus!
