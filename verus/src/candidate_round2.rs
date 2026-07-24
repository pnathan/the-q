// Under development (reported non-fatal). The V4 R3 magnitude tie-in: connect
// the grid step `1/2^s` to the relative error bound `2^-60·max(1,|v|)` (B = 60),
// using the per-magnitude choice `s = 61 − e` where `2^e ≤ |v|`.

use vstd::prelude::*;

verus! {

pub open spec fn pow2(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 } else { 2 * pow2((n - 1) as nat) }
}

pub proof fn pow2_pos(n: nat)
    ensures pow2(n) >= 1,
    decreases n
{
    if n == 0 {} else { pow2_pos((n - 1) as nat); }
}

/// `pow2(n + 1) == 2 * pow2(n)` (single-step unfold).
pub proof fn pow2_step(n: nat)
    ensures pow2(n + 1) == 2 * pow2(n),
{
    // pow2(n+1) unfolds to 2*pow2((n+1-1) as nat) == 2*pow2(n) since n+1 > 0.
}

/// `pow2(a + b) == pow2(a) * pow2(b)`.
pub proof fn pow2_adds(a: nat, b: nat)
    ensures pow2(a + b) == pow2(a) * pow2(b),
    decreases b
{
    if b == 0 {
    } else {
        let bm = (b - 1) as nat;
        pow2_adds(a, bm);                        // pow2(a + bm) == pow2(a) * pow2(bm)
        assert(b == bm + 1);
        assert(a + b == (a + bm) + 1);
        pow2_step(a + bm);                       // pow2((a+bm)+1) == 2*pow2(a+bm)
        pow2_step(bm);                           // pow2(bm+1)     == 2*pow2(bm)
        // congruence (a+b == (a+bm)+1, b == bm+1) gives:
        assert(pow2(a + b) == 2 * pow2(a + bm));
        assert(pow2(b) == 2 * pow2(bm));
        assert(pow2(a + b) == pow2(a) * pow2(b)) by (nonlinear_arith)
            requires
                pow2(a + b) == 2 * pow2(a + bm),
                pow2(a + bm) == pow2(a) * pow2(bm),
                pow2(b) == 2 * pow2(bm);
    }
}

/// **R3 magnitude tie-in.** For a value `v = n_abs/d` with `2^e ≤ v`
/// (`pow2(e)·d ≤ n_abs`) and the grid exponent `s = 61 − e`, the grid step is
/// within the relative bound: `d·2^60 < n_abs·2^s`, i.e. `1/2^s < 2^-60·v`.
/// Since the grid error is `< 1/2^s`, this gives `error < 2^-60·v ≤ 2^-60·max(1,v)`.
pub proof fn r3_relative_bound(n_abs: nat, d: int, e: nat, s: nat)
    requires
        d >= 1,
        e <= 61,
        s == (61 - e) as nat,
        (pow2(e) as int) * d <= n_abs as int,
    ensures
        d * (pow2(60) as int) < (n_abs as int) * (pow2(s) as int),
{
    pow2_pos(e);
    pow2_pos(s);
    pow2_pos(60);
    pow2_adds(e, s);                       // pow2(e+s) == pow2(e)*pow2(s); e+s == 61
    assert(e + s == 61);
    assert(pow2(61) == pow2(e) * pow2(s));
    assert(pow2(61) == 2 * pow2(60));      // definitional unfold
    // d*2^60 < d*2^61 == d*pow2(e)*pow2(s) <= n_abs*pow2(s)
    assert(d * (pow2(60) as int) < (n_abs as int) * (pow2(s) as int)) by (nonlinear_arith)
        requires
            d >= 1,
            (pow2(e) as int) * d <= n_abs as int,
            (pow2(61) as int) == (pow2(e) as int) * (pow2(s) as int),
            (pow2(61) as int) == 2 * (pow2(60) as int),
            (pow2(60) as int) >= 1,
            (pow2(s) as int) >= 1;
}

/// The `|v| ≤ 1` case: with `s ≥ 60`, the grid step is `≤ 2^-60` in absolute
/// terms (`= 2^-60·max(1,v)` since `max(1,v)=1`). Division-free: `pow2(60) ≤ pow2(s)`.
pub proof fn r3_small_case(s: nat)
    requires s >= 60,
    ensures pow2(60) <= pow2(s),
{
    let k = (s - 60) as nat;
    pow2_adds(60, k);                     // pow2(60 + k) == pow2(60) * pow2(k)
    assert(60 + k == s);
    pow2_pos(k);
    pow2_pos(60);
    assert(pow2(s) == pow2(60) * pow2(k));
    assert(pow2(60) <= pow2(s)) by (nonlinear_arith)
        requires pow2(s) == pow2(60) * pow2(k), pow2(k) >= 1, pow2(60) >= 1;
}

fn main() {}

}
