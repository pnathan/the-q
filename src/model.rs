//! The ghost model: the mathematics that `Rat` is specified against.
//!
//! Everything here is `spec`/`proof` code. Plain rustc erases it, and Verus
//! consumes it. Two disciplines apply throughout:
//!
//! 1. **Unbounded arithmetic.** Specifications talk about Verus `int`/`nat`, not
//!    about `i64`/`i128`. The machine types appear only in the executable code,
//!    where their ranges are discharged as proof obligations (V2).
//! 2. **Division-free value specifications.** No specification of a *value*
//!    uses `/`. "`r` is `a + b`" is written by cross-multiplication:
//!    `r.num * (a.den * b.den) == (a.num * b.den + b.num * a.den) * r.den`.
//!    SMT solvers handle nonlinear multiplication badly and division far worse.
//!    The Lean formalisation of the same mathematics follows the same
//!    discipline. (Division does appear inside *definitional* spec functions
//!    such as `gcd_nat`. There it is unavoidable, and the recursion carries the
//!    meaning instead of the solver.)

use verus_builtin_macros::verus;

#[allow(unused_imports)]
use verus_builtin::*;
#[allow(unused_imports)]
use vstd::prelude::*;

#[allow(unused_imports)]
use crate::types::{MAX_MAG, Rat};

verus! {

// ---------------------------------------------------------------------------
// Elementary number theory
// ---------------------------------------------------------------------------

/// `2^n` as an unbounded integer.
pub open spec fn pow2(n: nat) -> int
    decreases n,
{
    if n == 0 {
        1int
    } else {
        2 * pow2((n - 1) as nat)
    }
}

/// `10^n` as an unbounded integer.
///
/// The decimal counterpart of [`pow2`], and it exists for the same reason.
/// `from_decimal` cannot state *what value it produces* without a spec-level
/// name for its scale factor. This function applies only at
/// `n <= MAX_DEC_PLACES`.
pub open spec fn pow10(n: nat) -> int
    decreases n,
{
    if n == 0 {
        1int
    } else {
        10 * pow10((n - 1) as nat)
    }
}

/// Absolute value on `int`.
pub open spec fn abs_int(x: int) -> int {
    if x >= 0 { x } else { -x }
}

/// `max` on `int`.
pub open spec fn max_int(a: int, b: int) -> int {
    if a >= b { a } else { b }
}

/// `d` divides `n`.
///
/// The `#[trigger]` is mandatory. The only candidate term is a multiplication,
/// and Verus does not pick an arithmetic operator as a trigger on its own.
pub open spec fn divides(d: int, n: int) -> bool {
    exists|k: int| n == #[trigger] (d * k)
}

/// Euclid's greatest common divisor, defined by structural recursion on the
/// second argument (this is the termination measure discharged in V5).
///
/// `gcd_nat(a, 0) == a`, and `gcd_nat(0, 0) == 0`.
pub open spec fn gcd_nat(a: nat, b: nat) -> nat
    decreases b,
{
    if b == 0 {
        a
    } else {
        gcd_nat(b, (a % b) as nat)
    }
}

/// `gcd` lifted to integers via absolute values. This is the value that `Rat`
/// canonicality refers to.
pub open spec fn gcd_int(a: int, b: int) -> int {
    gcd_nat(abs_int(a) as nat, abs_int(b) as nat) as int
}

/// Bit length: the least `k` with `x < 2^k`, for `x >= 0`. `bitlen(0) == 0`.
pub open spec fn bitlen(x: int) -> nat
    decreases x,
{
    if x <= 0 {
        0nat
    } else {
        (bitlen(x / 2) + 1) as nat
    }
}

// ---------------------------------------------------------------------------
// The budget, in ghost form
// ---------------------------------------------------------------------------

/// The magnitude budget `2^62 - 1` as an unbounded integer.
pub open spec fn max_mag() -> int {
    MAX_MAG as int
}

/// The I2 half of the type invariant, stated on a raw fraction.
pub open spec fn fits_budget(n: int, d: int) -> bool {
    &&& abs_int(n) <= max_mag()
    &&& d <= max_mag()
}

/// Whether the *value* `n / d` (with `d > 0`) is representable at all, that is
/// `|n/d| <= MAX_MAG`. Written division-free.
///
/// When this predicate fails, the value is outside the representable range and
/// R3 does not apply. The operations saturate to `±MAX_MAG/1`, and the
/// `checked_*` variants return `None`.
///
/// The exclusion is a choice, not a forced move. Some unrepresentable values do
/// have a `Rat` inside the R3 bound. For example, `n/d = MAX_MAG + 1/2` lies
/// within `2^-61` of `MAX_MAG/1`. The exclusion keeps the contract on a single
/// clean side of a boundary. It is not a consequence of an empty candidate set.
pub open spec fn magnitude_fits(n: int, d: int) -> bool {
    abs_int(n) <= max_mag() * d
}

// ---------------------------------------------------------------------------
// The type invariant (V1)
// ---------------------------------------------------------------------------

impl Rat {
    /// The full type invariant: I1 (canonical) and I2 (bounded).
    ///
    /// Every public function `requires` this of its inputs and `ensures` it of
    /// its outputs. That obligation is V1.
    pub open spec fn wf(self) -> bool {
        &&& self.den > 0
        &&& gcd_int(self.num as int, self.den as int) == 1
        &&& (self.num == 0 ==> self.den == 1)
        &&& abs_int(self.num as int) <= max_mag()
        &&& (self.den as int) <= max_mag()
    }

    /// The numerator, as an unbounded integer.
    pub open spec fn n(self) -> int {
        self.num as int
    }

    /// The denominator, as an unbounded integer.
    pub open spec fn d(self) -> int {
        self.den as int
    }
}

// ---------------------------------------------------------------------------
// The relational model: order and equality, division-free
// ---------------------------------------------------------------------------

/// Mathematical equality of two rationals. For canonical `Rat` this coincides
/// with structural equality (proved as `lemma_canonical_eq` in [`crate::laws`]).
pub open spec fn q_eq(a: Rat, b: Rat) -> bool {
    a.n() * b.d() == b.n() * a.d()
}

/// `a <= b`. Valid as written because both denominators are positive.
pub open spec fn q_le(a: Rat, b: Rat) -> bool {
    a.n() * b.d() <= b.n() * a.d()
}

/// `a < b`.
pub open spec fn q_lt(a: Rat, b: Rat) -> bool {
    a.n() * b.d() < b.n() * a.d()
}

/// `r` is exactly the value of the fraction `n / d` (with `d > 0`).
///
/// This is *the* value-correctness predicate. It uses division-free
/// cross-multiplication, as the module header states.
pub open spec fn q_is(r: Rat, n: int, d: int) -> bool {
    r.n() * d == n * r.d()
}

/// `r <= n / d`.
pub open spec fn q_le_frac(r: Rat, n: int, d: int) -> bool {
    r.n() * d <= n * r.d()
}

/// `r >= n / d`.
pub open spec fn q_ge_frac(r: Rat, n: int, d: int) -> bool {
    r.n() * d >= n * r.d()
}

// ---------------------------------------------------------------------------
// The R3 error bound, division-free
// ---------------------------------------------------------------------------

/// The precision exponent `B` of the rounding contract. R3 is
/// `|result - exact| <= 2^-B · max(1, |exact|)`. The specification's acceptance
/// bar is `B >= 60`, and the dyadic-snap implementation achieves 61.
///
/// The extra bit over `60` comes from the use of the whole budget on the scaled
/// numerator. The implementation reserves no headroom against a rounding carry.
/// See [`crate::round::snap_shift`]. It handles the carry at the point of
/// occurrence rather than prevents the carry by construction.
pub open spec fn precision_b() -> nat {
    61nat
}

/// R3, division-free.
///
/// The real statement is `|r - n/d| <= 2^-61 · max(1, |n/d|)`. Multiplication
/// through by `r.den · d · 2^61` (both denominators positive) gives
/// `|r.num·d - n·r.den| · 2^61 <= r.den · max(d, |n|)`. That inequality is the
/// form written here, and it contains no division.
pub open spec fn within_error_bound(r: Rat, n: int, d: int) -> bool {
    abs_int(r.n() * d - n * r.d()) * pow2(precision_b()) <= r.d() * max_int(d, abs_int(n))
}

/// The precision that `Dir::Nearest` achieves: a *half* grid step rather than a
/// whole one. The nearest integer is never more than half a unit from the exact
/// scaled value (`lemma_grid_error_step_nearest_half` in `round.rs`).
///
/// This bound is **not** the crate-wide R3 contract. `precision_b` stays at
/// `61`, because the directed modes (`Dir::Down`, `Dir::Up`) achieve no better
/// than that. The tighter bound holds on the path that every default operation
/// (`Rat::add`/`sub`/`mul`/`div`) takes. A proof gives it as an additional
/// guarantee beside the uniform one, not in place of it.
pub open spec fn precision_b_nearest() -> nat {
    62nat
}

/// R3 at `Dir::Nearest`'s tighter bound, division-free. Same shape as
/// `within_error_bound`, at `B = 62` instead of `61`.
pub open spec fn within_error_bound_nearest(r: Rat, n: int, d: int) -> bool {
    abs_int(r.n() * d - n * r.d()) * pow2(precision_b_nearest()) <= r.d() * max_int(
        d,
        abs_int(n),
    )
}

/// The accumulated bound after `k` operations: `k · 2^-B · max(1, |exact|)`.
/// Used by the n-ary helpers (V8).
pub open spec fn within_error_bound_k(r: Rat, n: int, d: int, k: nat) -> bool {
    abs_int(r.n() * d - n * r.d()) * pow2(precision_b()) <= (k as int) * r.d() * max_int(
        d,
        abs_int(n),
    )
}

/// `|r - n/d| <= k · m / 2^B`, division-free.
///
/// The *absolute* form of the accumulated bound. It carries an explicit
/// magnitude bound `m` on the intermediates. A fold needs this absolute form
/// rather than a relative bound, and V8 proves it.
///
/// Relative error does not accumulate cleanly across a sum. Each step's R3
/// bound is measured against *that step's* value, and those values vary. The
/// induction therefore does not yield `k` relative units against the final
/// value. Absolute error does accumulate cleanly, because addition is exactly
/// 1-Lipschitz. On this crate's domain the two forms coincide: every engine
/// value lies in `[0, 1]`, so `max(1, |exact|) == 1` throughout and `m == 1`.
/// The bound is then `k · 2^-61` outright.
pub open spec fn within_abs_error(r: Rat, n: int, d: int, k: nat, m: int) -> bool {
    abs_int(r.n() * d - n * r.d()) * pow2(precision_b()) <= (k as int) * m * (r.d() * d)
}

// ---------------------------------------------------------------------------
// Basic lemmas about the above
// ---------------------------------------------------------------------------

/// `2^n > 0`.
pub proof fn lemma_pow2_pos(n: nat)
    ensures
        pow2(n) > 0,
    decreases n,
{
    if n == 0 {
    } else {
        lemma_pow2_pos((n - 1) as nat);
    }
}

/// `2^n` is monotone in `n`.
pub proof fn lemma_pow2_mono(a: nat, b: nat)
    requires
        a <= b,
    ensures
        pow2(a) <= pow2(b),
    decreases b,
{
    if a == b {
    } else {
        lemma_pow2_mono(a, (b - 1) as nat);
        lemma_pow2_pos((b - 1) as nat);
    }
}

/// `2^(a+b) == 2^a · 2^b`.
pub proof fn lemma_pow2_add(a: nat, b: nat)
    ensures
        pow2(a + b) == pow2(a) * pow2(b),
    decreases b,
{
    if b == 0 {
    } else {
        lemma_pow2_add(a, (b - 1) as nat);
        assert(pow2(a + b) == 2 * pow2((a + b - 1) as nat));
        assert(pow2(b) == 2 * pow2((b - 1) as nat));
        // A move of the factor of two across a product of two unknowns is
        // nonlinear. Z3 does not do it on its own.
        assert(2 * (pow2(a) * pow2((b - 1) as nat)) == pow2(a) * (2 * pow2(
            (b - 1) as nat,
        ))) by (nonlinear_arith);
    }
}

/// The characterising property of [`bitlen`]: `2^(k-1) <= x < 2^k` for `x > 0`.
pub proof fn lemma_bitlen_char(x: int)
    requires
        x >= 0,
    ensures
        x < pow2(bitlen(x)),
        x > 0 ==> pow2((bitlen(x) - 1) as nat) <= x,
    decreases x,
{
    if x <= 0 {
        assert(pow2(0) == 1);
    } else {
        lemma_bitlen_char(x / 2);
        assert(x / 2 * 2 <= x < x / 2 * 2 + 2) by (nonlinear_arith);
        assert(pow2(bitlen(x)) == 2 * pow2(bitlen(x / 2)));
        if bitlen(x / 2) == 0 {
            assert(x / 2 == 0);
            assert(pow2(bitlen(x)) == 2);
        }
    }
}

/// [`bitlen`] is monotone.
pub proof fn lemma_bitlen_mono(x: int, y: int)
    requires
        0 <= x <= y,
    ensures
        bitlen(x) <= bitlen(y),
    decreases y,
{
    if x <= 0 {
    } else {
        assert(x / 2 <= y / 2) by (nonlinear_arith)
            requires
                0 < x <= y,
        ;
        lemma_bitlen_mono(x / 2, y / 2);
    }
}

/// `divides` is reflexive on non-zero integers, and everything divides zero.
pub proof fn lemma_divides_basic(d: int)
    ensures
        divides(d, d),
        divides(d, 0),
{
    assert(d == d * 1);
    assert(0 == d * 0);
}

/// Divisibility is preserved by integer linear combination.
pub proof fn lemma_divides_linear(d: int, a: int, b: int, s: int, t: int)
    requires
        divides(d, a),
        divides(d, b),
    ensures
        divides(d, s * a + t * b),
{
    let ka = choose|k: int| a == #[trigger] (d * k);
    let kb = choose|k: int| b == #[trigger] (d * k);
    assert(s * a + t * b == d * (s * ka + t * kb)) by (nonlinear_arith)
        requires
            a == d * ka,
            b == d * kb,
    ;
}

/// Divisibility is transitive.
pub proof fn lemma_divides_trans(a: int, b: int, c: int)
    requires
        divides(a, b),
        divides(b, c),
    ensures
        divides(a, c),
{
    let k1 = choose|k: int| b == #[trigger] (a * k);
    let k2 = choose|k: int| c == #[trigger] (b * k);
    assert(c == a * (k1 * k2)) by (nonlinear_arith)
        requires
            b == a * k1,
            c == b * k2,
    ;
}

/// A non-negative divisor of `1` is `1`.
///
/// The unit case of divisibility, and the last step of each coprimality proof
/// in [`crate::gcd`]: a gcd that divides `1` is `1`.
pub proof fn lemma_divides_one(d: int)
    requires
        divides(d, 1int),
        d >= 0,
    ensures
        d == 1,
{
    let k = choose|k: int| 1int == #[trigger] (d * k);
    assert(d > 0) by (nonlinear_arith)
        requires
            1int == d * k,
            d >= 0,
    ;
    lemma_divides_le(d, 1int);
}

// ---------------------------------------------------------------------------
// Concrete powers of two
//
// These are the exponents the crate needs as literals. Each unfolding step of
// `pow2` is cheap, but the unfolding depth is linear in the exponent. Each
// value is therefore pinned once here and reused, rather than re-derived at
// every use site.
// ---------------------------------------------------------------------------

/// `2^0` and `2^1`.
///
/// These two facts still need a proof. `pow2` is recursive with default fuel 1,
/// so `pow2(1)` unfolds to `2 · pow2(0)` and then stops. The solver does not
/// reach the base case on its own.
pub proof fn lemma_pow2_small()
    ensures
        pow2(0) == 1,
        pow2(1) == 2,
{
    reveal_with_fuel(pow2, 3);
}


/// `2^61`.
pub proof fn lemma_pow2_61()
    ensures
        pow2(61) == 2305843009213693952,
{
    reveal_with_fuel(pow2, 62);
}

/// `2^62`.
pub proof fn lemma_pow2_62()
    ensures
        pow2(62) == 4611686018427387904,
{
    reveal_with_fuel(pow2, 63);
}

/// `2^64`.
pub proof fn lemma_pow2_64()
    ensures
        pow2(64) == 18446744073709551616,
{
    reveal_with_fuel(pow2, 65);
}

/// `2^124`.
///
/// Above roughly `2^64`, `reveal_with_fuel` is not a usable proof. The
/// unfolding is linear in the exponent, and Z3 exhausts its resource limit
/// before it reaches the literal. A square of an already pinned value costs one
/// multiplication instead.
pub proof fn lemma_pow2_124()
    ensures
        pow2(124) == 21267647932558653966460912964485513216,
{
    lemma_pow2_62();
    lemma_pow2_add(62, 62);
}

/// `2^125`.
pub proof fn lemma_pow2_125()
    ensures
        pow2(125) == 42535295865117307932921825928971026432,
{
    lemma_pow2_124();
    assert(pow2(125) == 2 * pow2(124));
}

/// `2^126`.
pub proof fn lemma_pow2_126()
    ensures
        pow2(126) == 85070591730234615865843651857942052864,
{
    lemma_pow2_125();
    assert(pow2(126) == 2 * pow2(125));
}

/// The budget in terms of powers of two: `MAX_MAG == 2^62 - 1`, and `2^61`
/// (the largest snapped denominator) is comfortably inside it.
pub proof fn lemma_max_mag_pow2()
    ensures
        max_mag() == pow2(62) - 1,
        pow2(61) <= max_mag(),
        max_mag() > 0,
{
    lemma_pow2_61();
    lemma_pow2_62();
}

/// A product of two budget-sized integers fits comfortably in `i128`.
pub proof fn lemma_mul_in_i128(x: int, y: int)
    requires
        abs_int(x) <= max_mag(),
        abs_int(y) <= max_mag(),
    ensures
        abs_int(x * y) < pow2(124),
{
    lemma_max_mag_pow2();
    lemma_pow2_62();
    lemma_pow2_124();
    assert(abs_int(x * y) == abs_int(x) * abs_int(y)) by (nonlinear_arith)
        requires
            abs_int(x) == (if x >= 0 { x } else { -x }),
            abs_int(y) == (if y >= 0 { y } else { -y }),
    ;
    assert(abs_int(x) * abs_int(y) <= max_mag() * max_mag()) by (nonlinear_arith)
        requires
            0 <= abs_int(x) <= max_mag(),
            0 <= abs_int(y) <= max_mag(),
    ;
    assert(max_mag() * max_mag() < pow2(124)) by (nonlinear_arith)
        requires
            max_mag() == 4611686018427387903,
            pow2(124) == 21267647932558653966460912964485513216,
    ;
}

/// `|x · c| == |x| · c` for positive `c`.
///
/// This fact applies whenever a denominator scales a bound. One statement here
/// removes the need to re-derive it inside a nonlinear goal at each call site.
pub proof fn lemma_abs_mul_pos(x: int, c: int)
    requires
        c > 0,
    ensures
        abs_int(x * c) == abs_int(x) * c,
{
    if x >= 0 {
        assert(x * c >= 0) by (nonlinear_arith)
            requires
                x >= 0,
                c > 0,
        ;
    } else {
        assert(x * c < 0) by (nonlinear_arith)
            requires
                x < 0,
                c > 0,
        ;
        assert(-(x * c) == (-x) * c) by (nonlinear_arith);
    }
}

/// `gcd(x, 1) == 1`.
///
/// This fact needs two unfoldings. `gcd(x, 1)` goes to `gcd(1, x % 1)`, which
/// is `gcd(1, 0)`, which is `1`. Verus gives a recursive spec function a default
/// fuel of one. The explicit `reveal_with_fuel` supplies the rest.
pub proof fn lemma_gcd_unit(x: int)
    ensures
        gcd_int(x, 1) == 1,
{
    reveal_with_fuel(gcd_nat, 3);
    assert(abs_int(x) % 1 == 0);
}

/// A positive divisor of a positive number is at most that number.
pub proof fn lemma_divides_le(d: int, n: int)
    requires
        d > 0,
        n > 0,
        divides(d, n),
    ensures
        d <= n,
{
    let k = choose|k: int| n == #[trigger] (d * k);
    assert(k >= 1) by (nonlinear_arith)
        requires
            d > 0,
            n > 0,
            n == d * k,
    ;
    assert(d * 1 <= d * k) by (nonlinear_arith)
        requires
            d > 0,
            k >= 1,
    ;
}

} // verus!
