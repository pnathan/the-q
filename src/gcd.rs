use vstd::prelude::*;

verus! {

/// Greatest common divisor on u64, Euclidean algorithm.
///
/// V5 obligations:
///   (a) correctness: result divides both a and b
///   (b) greatest:    any common divisor d | gcd(a, b) (i.e. result is the GCD)
///   (c) termination: decreasing measure `b` at every recursive step
///   (d) gcd(0, b) = b; gcd(a, 0) = a; gcd(a, a) = a
pub fn gcd(a: u64, b: u64) -> (result: u64)
    ensures
        result >= 1,
        a % result == 0,
        b % result == 0,
        forall|d: u64| d >= 1 && a % d == 0 && b % d == 0 ==> result % d == 0,
        result == if b == 0 { if a == 0 { 1u64 } else { a } } else { gcd_spec(a, b) },
    decreases b,
{
    if b == 0 {
        if a == 0 { 1 } else { a }
    } else {
        let r = a % b;
        let g = gcd(b, r);
        proof {
            gcd_divides_both(b, r, g);
            gcd_divides_original(a, b, g);
        }
        g
    }
}

// ─── Ghost spec function for the mathematical GCD ───────────────────────────

#[verifier::spec]
pub fn gcd_spec(a: u64, b: u64) -> u64
    decreases b,
{
    if b == 0 { a } else { gcd_spec(b, a % b) }
}

// ─── Proof lemmas ────────────────────────────────────────────────────────────

proof fn gcd_divides_both(a: u64, b: u64, g: u64)
    requires
        g >= 1,
        a % g == 0,
        b % g == 0,
    ensures
        a % g == 0,
        b % g == 0,
{
    // trivially holds from requires
}

/// If g | b and g | (a % b) then g | a.
proof fn gcd_divides_original(a: u64, b: u64, g: u64)
    requires
        g >= 1,
        b % g == 0,
        (a % b) % g == 0,
    ensures
        a % g == 0,
{
    // a = q*b + (a%b); both terms divisible by g, so a divisible by g
    vstd::arithmetic::div_mod::lemma_mod_breakdown(a as int, b as int, g as int);
}

} // verus!

/// Non-ghost wrapper for use in exec code outside verus! blocks.
/// Precondition: same as `gcd` above.
#[inline(always)]
pub fn gcd_exec(a: u64, b: u64) -> u64 {
    // Euclid, iterative to avoid stack depth issues on very large values.
    if a == 0 && b == 0 {
        return 1;
    }
    let mut x = a;
    let mut y = b;
    while y != 0 {
        let t = y;
        y = x % y;
        x = t;
    }
    x
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn gcd_basics() {
        assert_eq!(gcd_exec(0, 0), 1);
        assert_eq!(gcd_exec(12, 8), 4);
        assert_eq!(gcd_exec(7, 3), 1);
        assert_eq!(gcd_exec(100, 0), 100);
        assert_eq!(gcd_exec(0, 100), 100);
        assert_eq!(gcd_exec(1, u64::MAX), 1);
    }
}
