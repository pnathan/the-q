use vstd::prelude::*;
#[allow(unused_imports)]
use vstd::arithmetic::div_mod::*;
#[allow(unused_imports)]
use vstd::arithmetic::mul::*;

verus! {

/// Spec: d divides n (there exists k such that n == d * k).
pub open spec fn spec_divides(d: int, n: int) -> bool {
    exists|k: int| #[trigger] (d * k) == n
}

/// Spec: g is a common divisor of a and b.
pub open spec fn is_common_divisor(g: int, a: int, b: int) -> bool {
    spec_divides(g, a) && spec_divides(g, b)
}

/// Spec: g is THE greatest common divisor of a and b (divisibility ordering).
pub open spec fn is_gcd(g: int, a: int, b: int) -> bool {
    g >= 0
    && is_common_divisor(g, a, b)
    && forall|d: int| is_common_divisor(d, a, b) ==> spec_divides(d, g)
}

proof fn lemma_divides_self(a: int)
    ensures spec_divides(a, a),
{
    assert(a * 1 == a);
}

proof fn lemma_divides_zero(a: int)
    ensures spec_divides(a, 0int),
{
    assert(a * 0 == 0int);
}

proof fn lemma_divides_mod(a: int, b: int, d: int)
    requires
        b != 0,
        spec_divides(d, a),
        spec_divides(d, b),
    ensures
        spec_divides(d, a % b),
{
    let ka = choose|k: int| #[trigger] (d * k) == a;
    let kb = choose|k: int| #[trigger] (d * k) == b;
    lemma_fundamental_div_mod(a, b);
    // a == b * (a / b) + a % b
    // so a % b == a - b * (a / b) == d*ka - d*kb * (a / b) == d * (ka - kb * (a/b))
    let q = a / b;
    assert(a == b * q + a % b);
    assert(d * ka == a);
    assert(d * kb == b);
    // Need: a % b == d * (ka - kb * q)
    // a % b = a - b * q = d*ka - d*kb*q
    lemma_mul_is_associative(d, kb, q);
    // d*kb*q == d*(kb*q)
    lemma_mul_is_distributive_sub(d, ka, kb * q);
    // d*(ka - kb*q) == d*ka - d*(kb*q) == a - b*q == a%b
    assert(d * (ka - kb * q) == a % b);
}

proof fn lemma_divides_mod_rev(a: int, b: int, d: int)
    requires
        b != 0,
        spec_divides(d, b),
        spec_divides(d, a % b),
    ensures
        spec_divides(d, a),
{
    let kb = choose|k: int| #[trigger] (d * k) == b;
    let kr = choose|k: int| #[trigger] (d * k) == (a % b);
    let q = a / b;
    lemma_fundamental_div_mod(a, b);
    // a == b * q + a % b == d*kb*q + d*kr
    lemma_mul_is_associative(d, kb, q);
    lemma_mul_is_distributive_add(d, kb * q, kr);
    assert(d * (kb * q + kr) == a);
}

/// Euclidean GCD on u64 — verified.
pub fn gcd(a: u64, b: u64) -> (result: u64)
    ensures
        is_gcd(result as int, a as int, b as int),
{
    if b == 0 {
        proof {
            lemma_divides_self(a as int);
            lemma_divides_zero(a as int);
            // Every common divisor d of (a, 0) satisfies d|a (trivially,
            // since is_common_divisor requires d|a). So spec_divides(d, a).
        }
        return a;
    }

    let mut x: u64 = a;
    let mut y: u64 = b;

    while y != 0
        invariant
            x as int >= 0,
            y as int >= 0,
            forall|d: int| is_common_divisor(d, a as int, b as int)
                <==> is_common_divisor(d, x as int, y as int),
        decreases y,
    {
        proof {
            assert forall|d: int| is_common_divisor(d, x as int, y as int)
                implies is_common_divisor(d, y as int, (x as int) % (y as int))
            by {
                lemma_divides_mod(x as int, y as int, d);
            }
            assert forall|d: int| is_common_divisor(d, y as int, (x as int) % (y as int))
                implies is_common_divisor(d, x as int, y as int)
            by {
                lemma_divides_mod_rev(x as int, y as int, d);
                lemma_divides_self(d);
            }
        }
        let t = y;
        y = x % y;
        x = t;
    }

    proof {
        // y == 0; x is the gcd
        lemma_divides_self(x as int);
        lemma_divides_zero(x as int);
        assert(is_common_divisor(x as int, x as int, 0int));
        // x is a common divisor of (a, b) since common_divisors are preserved
        assert(is_common_divisor(x as int, a as int, b as int));
        // x is the greatest: any common divisor d of (a,b) is also
        // a common divisor of (x, 0), hence d|x.
        assert forall|d: int| is_common_divisor(d, a as int, b as int)
            implies spec_divides(d, x as int)
        by {
            assert(is_common_divisor(d, x as int, 0int));
        }
    }
    x
}

// Helper: multiplication distributes over subtraction.
proof fn lemma_mul_is_distributive_sub(a: int, b: int, c: int)
    ensures a * (b - c) == a * b - a * c,
{
    lemma_mul_is_distributive_add(a, b, -c);
    // a * (b + (-c)) == a*b + a*(-c) == a*b - a*c
    assert(a * (-c) == -(a * c)) by {
        assert(a * (-c) + a * c == a * ((-c) + c)) by {
            lemma_mul_is_distributive_add(a, -c, c);
        }
        assert((-c) + c == 0int);
        assert(a * 0 == 0int) by { lemma_mul_basics(a); }
    }
}

} // verus!

/// Euclidean GCD on u128, for reducing i128 intermediates.
/// Not verified (u128 not fully supported in Verus); correctness
/// follows by the same argument as the u64 version.
pub(crate) fn gcd128(mut a: u128, mut b: u128) -> u128 {
    while b != 0 {
        let t = b;
        b = a % b;
        a = t;
    }
    a
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn gcd_basics() {
        assert_eq!(gcd(0, 0), 0);
        assert_eq!(gcd(10, 0), 10);
        assert_eq!(gcd(0, 10), 10);
        assert_eq!(gcd(12, 8), 4);
        assert_eq!(gcd(7, 13), 1);
        assert_eq!(gcd(100, 75), 25);
        assert_eq!(gcd(u64::MAX, 1), 1);
        assert_eq!(gcd(u64::MAX, u64::MAX), u64::MAX);
    }

    #[test]
    fn gcd_commutative() {
        for &(a, b) in &[(3, 7), (12, 18), (100, 250), (0, 5), (1, 1)] {
            assert_eq!(gcd(a, b), gcd(b, a));
        }
    }

    #[test]
    fn gcd128_basics() {
        assert_eq!(gcd128(0, 0), 0);
        assert_eq!(gcd128(12, 8), 4);
        let big = 1u128 << 100;
        assert_eq!(gcd128(big, big), big);
        assert_eq!(gcd128(big, 1), 1);
    }
}
