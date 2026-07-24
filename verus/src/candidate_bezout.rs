// Under development (reported non-fatal). Bézout -> Euclid's lemma -> V1
// canonical uniqueness (value equality of two reduced fractions is structural
// equality). Self-contained.

use vstd::prelude::*;
use vstd::arithmetic::div_mod::lemma_fundamental_div_mod;

verus! {

pub open spec fn gcd(a: nat, b: nat) -> nat
    decreases b
{
    if b == 0 { a } else { gcd(b, (a % b) as nat) }
}

pub open spec fn divides(d: int, n: int) -> bool {
    exists|k: int| n == #[trigger] (d * k)
}

pub open spec fn nat_abs(x: int) -> nat {
    if x < 0 { (-x) as nat } else { x as nat }
}

/// Bézout: `gcd(a,b) == a*x + b*y` for some integer `(x, y)`.
pub proof fn bezout(a: nat, b: nat) -> (r: (int, int))
    ensures gcd(a, b) as int == (a as int) * r.0 + (b as int) * r.1,
    decreases b
{
    if b == 0 {
        (1int, 0int)
    } else {
        let (x1, y1) = bezout(b, (a % b) as nat);
        assert(gcd(a, b) == gcd(b, (a % b) as nat));
        lemma_fundamental_div_mod(a as int, b as int);
        let quo = (a as int) / (b as int);
        let x = y1;
        let y = x1 - quo * y1;
        assert(gcd(a, b) as int == (a as int) * x + (b as int) * y) by (nonlinear_arith)
            requires
                gcd(a, b) as int == (b as int) * x1 + ((a % b) as int) * y1,
                (a as int) == (b as int) * quo + (a as int) % (b as int),
                (a % b) as int == (a as int) % (b as int),
                x == y1,
                y == x1 - quo * y1;
        (x, y)
    }
}

pub proof fn divides_scale(d: int, n: int, c: int)
    requires divides(d, n),
    ensures divides(d, n * c),
{
    let k = choose|k: int| n == #[trigger] (d * k);
    assert(n * c == d * (k * c)) by (nonlinear_arith) requires n == d * k;
}

pub proof fn divides_neg(d: int, n: int)
    requires divides(d, n),
    ensures divides(d, -n),
{
    let k = choose|k: int| n == #[trigger] (d * k);
    assert(-n == d * (-k)) by (nonlinear_arith) requires n == d * k;
}

/// `|u| * v` is divisible by `m` whenever `u * v` is (sign only).
pub proof fn divides_abs_mul(m: int, u: int, v: int)
    requires divides(m, u * v),
    ensures divides(m, (nat_abs(u) as int) * v),
{
    if u < 0 {
        divides_neg(m, u * v);
        assert((nat_abs(u) as int) * v == -(u * v)) by (nonlinear_arith) requires u < 0;
    } else {
        assert((nat_abs(u) as int) * v == u * v) by (nonlinear_arith) requires u >= 0;
    }
}

/// Euclid's lemma: if `gcd(|u|, m) == 1` and `m | u*v`, then `m | v`.
pub proof fn euclid(m: nat, u: int, v: int)
    requires
        m >= 1,
        gcd(nat_abs(u), m) == 1,
        divides(m as int, u * v),
    ensures divides(m as int, v),
{
    let (x, y) = bezout(nat_abs(u), m);
    // 1 == |u|*x + m*y
    assert(1int == (nat_abs(u) as int) * x + (m as int) * y);
    // m | |u|*v
    divides_abs_mul(m as int, u, v);
    let t = choose|k: int| (nat_abs(u) as int) * v == #[trigger] ((m as int) * k);
    // v == (|u|*v)*x + m*(v*y) == m*t*x + m*(v*y) == m*(t*x + v*y)
    assert(v == (m as int) * (t * x + v * y)) by (nonlinear_arith)
        requires
            1int == (nat_abs(u) as int) * x + (m as int) * y,
            (nat_abs(u) as int) * v == (m as int) * t;
}

/// Mutual divisibility of positives implies equality.
pub proof fn divides_antisym(a: int, b: int)
    requires a >= 1, b >= 1, divides(a, b), divides(b, a),
    ensures a == b,
{
    let k = choose|k: int| b == #[trigger] (a * k);
    let j = choose|k: int| a == #[trigger] (b * k);
    // a == a*k*j  =>  k*j == 1  =>  k == 1 (positive)
    assert(a == a * (k * j)) by (nonlinear_arith) requires b == a * k, a == b * j;
    assert(k * j == 1) by (nonlinear_arith) requires a == a * (k * j), a >= 1;
    assert(k == 1) by (nonlinear_arith) requires k * j == 1, a == a * k, a >= 1, b >= 1, b == a * k;
    assert(b == a * 1);
}

/// **V1 canonical uniqueness**: two reduced fractions with equal value are
/// structurally identical. `an/ad == bn/bd` (division-free) with both in lowest
/// terms (den > 0, coprime) implies `an == bn` and `ad == bd`.
pub proof fn canonical_unique(an: int, ad: int, bn: int, bd: int)
    requires
        ad >= 1,
        bd >= 1,
        gcd(nat_abs(an), ad as nat) == 1,
        gcd(nat_abs(bn), bd as nat) == 1,
        an * bd == bn * ad,
        // keep ad, bd within nat range for the `as nat` casts
        ad >= 0,
        bd >= 0,
    ensures an == bn, ad == bd,
{
    // ad | an*bd  (== bn*ad == ad*bn)
    assert(divides(ad, an * bd)) by {
        assert(an * bd == ad * bn) by (nonlinear_arith) requires an * bd == bn * ad;
    }
    euclid(ad as nat, an, bd);          // gcd(|an|,ad)=1 ∧ ad | an*bd ⟹ ad | bd
    // bd | bn*ad  (== an*bd == bd*an)
    assert(divides(bd, bn * ad)) by {
        assert(bn * ad == bd * an) by (nonlinear_arith) requires an * bd == bn * ad;
    }
    euclid(bd as nat, bn, ad);          // ⟹ bd | ad
    divides_antisym(ad, bd);            // ad == bd
    // an*bd == bn*ad with ad == bd > 0 ⟹ an == bn
    assert(an == bn) by (nonlinear_arith) requires an * bd == bn * ad, ad == bd, bd >= 1;
}

fn main() {}

}
