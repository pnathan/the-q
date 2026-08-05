//! Root and transcendental functions: accuracy against an exact oracle, and
//! totality over every state.
//!
//! These functions have no exact rational answer, so the checks are of two
//! kinds. **Accuracy** is measured by inverting the function exactly — `sqrt`'s
//! result is squared and compared to the input, `exp`'s is checked against a
//! series computed at far higher precision — so the oracle never needs to
//! compute an irrational value it cannot represent. **Totality** is checked by
//! sweeping every state and every awkward input and asserting only that a value
//! comes back well-formed and classified, never a panic.

mod common;

use common::{rat, zero as oracle_zero, Rng};
use malachite_q::Rational;
use the_q::{Rat, MAX_MAG, Q};

fn one() -> Rational {
    Rational::from_signeds(1i128, 1i128)
}

fn mag(r: &Rational) -> Rational {
    if *r < oracle_zero() {
        -r.clone()
    } else {
        r.clone()
    }
}

/// Relative error of `got` against `want`, as an exact rational.
fn rel_err(got: &Rational, want: &Rational) -> Rational {
    let d = mag(&(got.clone() - want.clone()));
    let scale = {
        let m = mag(want);
        if m > one() {
            m
        } else {
            one()
        }
    };
    d / scale
}

/// `2^-k` as an exact rational, for stating tolerances.
fn eps(k: u32) -> Rational {
    Rational::from_signeds(1i128, 1i128 << k)
}

/// The largest `k` with `e <= 2^-k`, i.e. how many bits of precision a worst
/// observed relative error corresponds to. Printing the raw rational is
/// useless — these have hundreds of digits.
fn precision_bits(e: &Rational) -> u32 {
    let mut k = 0u32;
    while k < 62 && *e <= eps(k + 1) {
        k += 1;
    }
    k
}

const SPECIALS: [Q; 5] = [Q::PosSat, Q::NegSat, Q::PosInf, Q::NegInf, Q::Nan];

fn states() -> Vec<Q> {
    let mut v = vec![
        Q::Number(Rat::new(0, 1).unwrap()),
        Q::Number(Rat::new(1, 1).unwrap()),
        Q::Number(Rat::new(-1, 1).unwrap()),
        Q::Number(Rat::new(1, 2).unwrap()),
        Q::Number(Rat::new(-1, 2).unwrap()),
        Q::Number(Rat::new(4, 1).unwrap()),
        Q::Number(Rat::new(MAX_MAG, 1).unwrap()),
        Q::Number(Rat::new(-MAX_MAG, 1).unwrap()),
        Q::Number(Rat::new(1, MAX_MAG).unwrap()),
    ];
    v.extend_from_slice(&SPECIALS);
    v
}

/// Every result must be well-formed and in exactly one class. This is the
/// no-panic, no-malformed-value guarantee, checked on the artifact.
fn assert_total(q: Q, what: &str) {
    if let Q::Number(x) = q {
        common::assert_wf(x, what);
    }
    let c = [q.is_number(), q.is_saturated(), q.is_infinite(), q.is_nan()]
        .iter()
        .filter(|b| **b)
        .count();
    assert_eq!(c, 1, "{what} produced an unclassified value: {q}");
}

// ===========================================================================
// sqrt
// ===========================================================================

#[test]
fn sqrt_matches_the_derived_special_table() {
    assert_eq!(Q::PosInf.sqrt(), Q::PosInf);
    assert_eq!(Q::NegInf.sqrt(), Q::Nan, "no real root of -inf");
    assert_eq!(Q::Nan.sqrt(), Q::Nan);
    assert_eq!(Q::NegSat.sqrt(), Q::Nan, "negative");
    // The one that surprises people: sqrt of (MAX_MAG, inf) is (2^31, inf),
    // which reaches far below MAX_MAG, so no saturation state is sound.
    assert_eq!(
        Q::PosSat.sqrt(),
        Q::Nan,
        "sqrt of a saturated value cannot claim to still be saturated"
    );
    assert_eq!(Q::zero().sqrt(), Q::zero(), "exact");
    assert_eq!(Q::neg_one().sqrt(), Q::Nan, "no real root of a negative");
}

#[test]
fn sqrt_is_exact_on_perfect_squares() {
    for k in 1i64..200 {
        let q = Q::Number(Rat::new(k * k, 1).unwrap());
        assert_eq!(
            q.sqrt(),
            Q::Number(Rat::new(k, 1).unwrap()),
            "sqrt({}) must be exactly {k}",
            k * k
        );
    }
    // Perfect squares of rationals too.
    assert_eq!(
        Q::Number(Rat::new(9, 16).unwrap()).sqrt(),
        Q::Number(Rat::new(3, 4).unwrap())
    );
}

#[test]
fn sqrt_squared_recovers_the_input() {
    // The accuracy check that needs no irrational oracle: square the result and
    // compare against the input exactly.
    let mut rng = Rng::new(0x5EED_0001);
    let mut worst = oracle_zero();
    for _ in 0..20_000 {
        let x = rng.q();
        if x.numerator() <= 0 {
            continue;
        }
        let q = Q::Number(x);
        match q.sqrt() {
            Q::Number(r) => {
                let sq = rat(r) * rat(r);
                let e = rel_err(&sq, &rat(x));
                if e > worst {
                    worst = e.clone();
                }
                assert!(
                    e <= eps(40),
                    "sqrt({x}) = {r}; squaring gives {sq}, relative error {e}"
                );
            }
            other => panic!("sqrt of a positive number must be a number, got {other}"),
        }
    }
    println!(
        "sqrt: worst relative error of r^2 vs x is 2^-{}",
        precision_bits(&worst)
    );
}

#[test]
fn sqrt_is_accurate_in_the_unit_interval() {
    // The crate's actual working domain, where accuracy matters most.
    let mut rng = Rng::new(0x5EED_0002);
    for _ in 0..20_000 {
        let x = rng.q_unit();
        if x.numerator() == 0 {
            continue;
        }
        if let Q::Number(r) = Q::Number(x).sqrt() {
            let sq = rat(r) * rat(r);
            assert!(
                rel_err(&sq, &rat(x)) <= eps(45),
                "sqrt({x}) = {r} is not accurate enough in [0,1]"
            );
            assert!(rat(r) >= oracle_zero(), "sqrt returned a negative root");
        } else {
            panic!("sqrt of a unit value must be a number");
        }
    }
}

#[test]
fn sqrt_is_monotone() {
    let mut rng = Rng::new(0x5EED_0003);
    for _ in 0..5_000 {
        let (a, b) = (rng.q_unit(), rng.q_unit());
        let (lo, hi) = if Rat::le(a, b) { (a, b) } else { (b, a) };
        let (sl, sh) = (Q::Number(lo).sqrt(), Q::Number(hi).sqrt());
        if let (Q::Number(x), Q::Number(y)) = (sl, sh) {
            // Allow the rounding slack: monotone up to the grid.
            let slack = eps(40);
            assert!(
                rat(x) <= rat(y) + slack,
                "sqrt is not monotone: sqrt({lo})={x} > sqrt({hi})={y}"
            );
        }
    }
}

#[test]
fn sqrt_is_total_and_never_panics() {
    for q in states() {
        assert_total(q.sqrt(), "sqrt");
    }
    let mut rng = Rng::new(0x5EED_0004);
    for _ in 0..20_000 {
        let n = rng.next_u64() as i64;
        let d = rng.next_u64() as i64;
        assert_total(Q::new(n, d).sqrt(), "sqrt");
    }
}

#[test]
fn isqrt_is_correct() {
    use the_q::transcendental::isqrt_i64;
    // Exhaustive over a dense low range, then the boundaries.
    for n in 0i64..10_000 {
        let r = isqrt_i64(n);
        assert!(r * r <= n, "isqrt({n}) = {r} is too large");
        assert!((r + 1) * (r + 1) > n, "isqrt({n}) = {r} is too small");
    }
    for n in [MAX_MAG, MAX_MAG - 1, 1 << 62, (1i64 << 31) * (1i64 << 31)] {
        if n > MAX_MAG {
            continue;
        }
        let r = isqrt_i64(n);
        assert!(
            (r as i128) * (r as i128) <= n as i128,
            "isqrt({n}) too large"
        );
        assert!(
            ((r + 1) as i128) * ((r + 1) as i128) > n as i128,
            "isqrt({n}) too small"
        );
    }
    let mut rng = Rng::new(0x5EED_0005);
    for _ in 0..50_000 {
        let n = (rng.next_u64() % (MAX_MAG as u64 + 1)) as i64;
        let r = isqrt_i64(n);
        assert!(
            (r as i128) * (r as i128) <= n as i128,
            "isqrt({n}) too large"
        );
        assert!(
            ((r + 1) as i128) * ((r + 1) as i128) > n as i128,
            "isqrt({n}) too small"
        );
    }
}

// ===========================================================================
// exp
// ===========================================================================

/// `exp(x)` to far higher precision than the crate can represent, by summing
/// the Maclaurin series over exact rationals until the term is below `2^-90`.
/// Independent of the implementation: no range reduction, no fixed term count.
fn oracle_exp(x: &Rational) -> Rational {
    let mut term = one();
    let mut sum = one();
    let tol = eps(90);
    for n in 1..400u32 {
        term = term * x.clone() / Rational::from_signeds(n as i128, 1i128);
        sum += term.clone();
        if mag(&term) < tol {
            break;
        }
    }
    sum
}

#[test]
fn exp_matches_the_derived_special_table() {
    assert_eq!(Q::PosInf.exp(), Q::PosInf);
    assert_eq!(Q::NegInf.exp(), Q::zero(), "exp(-inf) is exactly 0");
    assert_eq!(Q::Nan.exp(), Q::Nan);
    // exp of (MAX_MAG, inf) is (exp(MAX_MAG), inf), astronomically inside
    // PosSat's denotation.
    assert_eq!(Q::PosSat.exp(), Q::PosSat);
    // But exp of (-inf, -MAX_MAG) is (0, exp(-MAX_MAG)) — an interval that does
    // NOT contain zero, so Number(0) would be an unsound denotation.
    assert_eq!(
        Q::NegSat.exp(),
        Q::Nan,
        "exp(NegSat) must not claim the exact value zero"
    );
    assert_eq!(Q::zero().exp(), Q::one(), "exp(0) is exactly 1");
}

#[test]
fn exp_is_accurate_against_a_high_precision_series() {
    let mut rng = Rng::new(0x5EED_0010);
    let mut worst = oracle_zero();
    let mut worst_at = oracle_zero();
    for _ in 0..600 {
        // Arguments across the whole usable range, including the large ones
        // where range reduction and squaring do the most work.
        let x = rng.q_unit();
        let scale = (rng.below(80) as i64) - 40;
        let arg = Rat::new(scale, 1).unwrap();
        let q = Q::add(Q::Number(x), Q::Number(arg));
        let Q::Number(xv) = q else { continue };
        let want = oracle_exp(&rat(xv));
        match q.exp() {
            Q::Number(r) => {
                let e = rel_err(&rat(r), &want);
                if e > worst {
                    worst = e.clone();
                    worst_at = rat(xv);
                }
                assert!(
                    e <= eps(30),
                    "exp({xv}) = {r}, want ~{want}, relative error {e}"
                );
            }
            other => {
                // Only legitimate near the ends of the range.
                assert!(
                    rat(xv) > Rational::from_signeds(40i128, 1i128)
                        || rat(xv) < Rational::from_signeds(-40i128, 1i128),
                    "exp({xv}) left the Number class at {other}"
                );
            }
        }
    }
    println!(
        "exp: worst relative error 2^-{} (at x = {worst_at})",
        precision_bits(&worst)
    );
}

#[test]
fn exp_is_very_accurate_on_small_arguments() {
    // No range reduction happens for |x| <= 1/2, so no squaring amplifies the
    // error, and the result should be near the grid resolution.
    let mut rng = Rng::new(0x5EED_0011);
    let mut worst = oracle_zero();
    for _ in 0..5_000 {
        let x = rng.q_unit();
        let half = Rational::from_signeds(1i128, 2i128);
        if rat(x) > half {
            continue;
        }
        let want = oracle_exp(&rat(x));
        if let Q::Number(r) = Q::Number(x).exp() {
            let e = rel_err(&rat(r), &want);
            if e > worst {
                worst = e.clone();
            }
            assert!(e <= eps(50), "exp({x}) = {r} is not accurate enough");
        }
    }
    println!(
        "exp: worst relative error on |x| <= 1/2 is 2^-{}",
        precision_bits(&worst)
    );
}

#[test]
fn exp_saturates_and_underflows_at_the_stated_thresholds() {
    assert_eq!(Q::Number(Rat::new(45, 1).unwrap()).exp(), Q::PosSat);
    assert_eq!(Q::Number(Rat::new(100, 1).unwrap()).exp(), Q::PosSat);
    assert_eq!(Q::Number(Rat::new(-45, 1).unwrap()).exp(), Q::zero());
    assert_eq!(Q::Number(Rat::new(-100, 1).unwrap()).exp(), Q::zero());
    // `ln(MAX_MAG)` is about 42.98, so 43 genuinely overflows — the `44`
    // constant is only a cheap pre-check, and arguments between 42.98 and 44
    // saturate through the ordinary arithmetic instead. 42 is the last integer
    // whose exponential fits.
    assert!(
        Q::Number(Rat::new(42, 1).unwrap()).exp().is_number(),
        "exp(42) is about 1.7e18 and fits the budget"
    );
    assert_eq!(
        Q::Number(Rat::new(43, 1).unwrap()).exp(),
        Q::PosSat,
        "exp(43) is about 4.7e18, past MAX_MAG"
    );
}

#[test]
fn exp_is_monotone_and_positive() {
    let mut rng = Rng::new(0x5EED_0012);
    for _ in 0..5_000 {
        let a = (rng.below(60) as i64) - 30;
        let b = a + 1 + (rng.below(5) as i64);
        let (ea, eb) = (
            Q::Number(Rat::new(a, 1).unwrap()).exp(),
            Q::Number(Rat::new(b, 1).unwrap()).exp(),
        );
        if let (Q::Number(x), Q::Number(y)) = (ea, eb) {
            assert!(rat(x) > oracle_zero(), "exp({a}) = {x} is not positive");
            assert!(rat(x) < rat(y), "exp is not increasing at ({a}, {b})");
        }
    }
}

#[test]
fn exp_is_total_and_never_panics() {
    for q in states() {
        assert_total(q.exp(), "exp");
    }
    let mut rng = Rng::new(0x5EED_0013);
    for _ in 0..20_000 {
        let n = rng.next_u64() as i64;
        let d = rng.next_u64() as i64;
        assert_total(Q::new(n, d).exp(), "exp");
    }
}

// ===========================================================================
// ln
// ===========================================================================

/// `ln(x)` to high precision, via `2·atanh((x-1)/(x+1))` over exact rationals
/// with its own binary reduction — structurally the same identity but carried
/// to 2^-90 with no fixed term count, so a term-count or reduction-bound bug in
/// the implementation shows up as disagreement.
fn oracle_ln(x: &Rational) -> Rational {
    let two = Rational::from_signeds(2i128, 1i128);
    let half = Rational::from_signeds(1i128, 2i128);
    let mut m = x.clone();
    let mut k = 0i64;
    while m > two {
        m /= two.clone();
        k += 1;
    }
    while m < half {
        m *= two.clone();
        k -= 1;
    }
    let z = (m.clone() - one()) / (m + one());
    let z2 = z.clone() * z.clone();
    let mut term = z.clone();
    let mut sum = z;
    let tol = eps(90);
    for j in 1..400u32 {
        term *= z2.clone();
        let add = term.clone() / Rational::from_signeds((2 * j + 1) as i128, 1i128);
        sum += add.clone();
        if mag(&add) < tol {
            break;
        }
    }
    let ln_m = two.clone() * sum;
    // ln 2 by the same series at z = 1/3.
    let z = Rational::from_signeds(1i128, 3i128);
    let z2 = z.clone() * z.clone();
    let mut term = z.clone();
    let mut s2 = z;
    for j in 1..400u32 {
        term *= z2.clone();
        let add = term.clone() / Rational::from_signeds((2 * j + 1) as i128, 1i128);
        s2 += add.clone();
        if mag(&add) < tol {
            break;
        }
    }
    ln_m + Rational::from_signeds(k as i128, 1i128) * two * s2
}

#[test]
fn ln2_constant_is_accurate() {
    let want = oracle_ln(&two_rational());
    match the_q::transcendental::ln2() {
        Q::Number(r) => {
            let e = rel_err(&rat(r), &want);
            println!("ln2: relative error 2^-{}", precision_bits(&e));
            assert!(e <= eps(55), "ln2 = {r} is not accurate enough");
        }
        other => panic!("ln2 must be a number, got {other}"),
    }
}

fn two_rational() -> Rational {
    Rational::from_signeds(2i128, 1i128)
}

#[test]
fn ln_matches_the_derived_special_table() {
    assert_eq!(Q::PosInf.ln(), Q::PosInf);
    assert_eq!(Q::NegInf.ln(), Q::Nan);
    assert_eq!(Q::Nan.ln(), Q::Nan);
    assert_eq!(Q::NegSat.ln(), Q::Nan, "negative");
    // ln of (MAX_MAG, inf) is about (43, inf), which reaches far below
    // MAX_MAG, so no saturation state is sound.
    assert_eq!(Q::PosSat.ln(), Q::Nan);
    assert_eq!(Q::zero().ln(), Q::NegInf, "the exact limit");
    assert_eq!(Q::neg_one().ln(), Q::Nan, "no real logarithm of a negative");
}

#[test]
fn ln_of_one_is_zero_and_ln_is_accurate() {
    // ln(1) should be exactly zero: z = 0 makes every series term vanish.
    assert_eq!(Q::one().ln(), Q::zero(), "ln(1) must be exactly 0");

    let mut rng = Rng::new(0x5EED_0020);
    let mut worst = oracle_zero();
    let mut worst_at = oracle_zero();
    for _ in 0..2_000 {
        let x = rng.q();
        if x.numerator() <= 0 {
            continue;
        }
        let want = oracle_ln(&rat(x));
        if let Q::Number(r) = Q::Number(x).ln() {
            let e = rel_err(&rat(r), &want);
            if e > worst {
                worst = e.clone();
                worst_at = rat(x);
            }
            assert!(e <= eps(40), "ln({x}) = {r}, want ~{want}");
        }
    }
    println!(
        "ln: worst relative error 2^-{} (at x = {worst_at})",
        precision_bits(&worst)
    );
}

#[test]
fn ln_inverts_exp_to_the_precision_the_grid_allows() {
    // The round-trip check, with the *right* bound — getting this wrong is
    // instructive, so the reasoning is written out.
    //
    // R3's error bound is `2^-61 · max(1, |exact|)`, which is **absolute**
    // below 1, not relative. So a small result carries fewer significant bits
    // than a large one: `exp(-30)` is about `2^-43`, and an absolute error of
    // `2^-61` there is a *relative* error of only `2^-18`. Since `ln` turns a
    // relative error in its argument into an absolute error in its result,
    // `ln(exp(-30))` is off by roughly `2^-61 · e^30`, which is about `5e-6`.
    //
    // That is a real property of the type, not a defect in either function, and
    // it is why the tolerance below scales with `max(1, e^-k)`.
    let mut rng = Rng::new(0x5EED_0021);
    let slack = Rational::from_signeds(1i128 << 12, 1i128);
    let mut worst_k = 0i64;
    let mut worst_bits = 64u32;
    for _ in 0..2_000 {
        let k = (rng.below(60) as i64) - 30;
        let x = Q::Number(Rat::new(k, 1).unwrap());
        let Q::Number(e) = x.exp() else { continue };
        let Q::Number(back) = Q::Number(e).ln() else {
            continue;
        };
        let d = mag(&(rat(back) - Rational::from_signeds(k as i128, 1i128)));
        // How small the intermediate got, which is what sets the precision.
        let scale = {
            let inv = oracle_exp(&Rational::from_signeds(-k as i128, 1i128));
            if inv > one() {
                inv
            } else {
                one()
            }
        };
        let bound = eps(61) * scale * slack.clone();
        assert!(
            d <= bound,
            "ln(exp({k})) = {back}, off by {d}, past the grid-limited bound"
        );
        if k <= 0 {
            let b = precision_bits(&d);
            if b < worst_bits {
                worst_bits = b;
                worst_k = k;
            }
        }
    }
    println!(
        "ln(exp(k)) round trip: worst absolute error 2^-{worst_bits} at k = {worst_k} \
         (small results carry fewer significant bits — R3 is absolute below 1)"
    );
}

#[test]
fn ln_is_monotone() {
    let mut rng = Rng::new(0x5EED_0022);
    for _ in 0..3_000 {
        let a = rng.q_nonzero();
        let b = rng.q_nonzero();
        if a.numerator() <= 0 || b.numerator() <= 0 {
            continue;
        }
        let (lo, hi) = if Rat::le(a, b) { (a, b) } else { (b, a) };
        if let (Q::Number(x), Q::Number(y)) = (Q::Number(lo).ln(), Q::Number(hi).ln()) {
            assert!(
                rat(x) <= rat(y) + eps(30),
                "ln is not monotone: ln({lo})={x} > ln({hi})={y}"
            );
        }
    }
}

#[test]
fn ln_is_total_and_never_panics() {
    for q in states() {
        assert_total(q.ln(), "ln");
    }
    let mut rng = Rng::new(0x5EED_0023);
    for _ in 0..20_000 {
        let n = rng.next_u64() as i64;
        let d = rng.next_u64() as i64;
        assert_total(Q::new(n, d).ln(), "ln");
    }
}

#[test]
fn pow_i32_handles_negative_exponents_totally() {
    let two = Q::Number(Rat::new(2, 1).unwrap());
    assert_eq!(two.pow_i32(3), Q::Number(Rat::new(8, 1).unwrap()));
    assert_eq!(two.pow_i32(0), Q::one());
    assert_eq!(two.pow_i32(-3), Q::Number(Rat::new(1, 8).unwrap()));
    // The case that would panic on a partial reciprocal.
    assert_eq!(Q::zero().pow_i32(-1), Q::PosInf);
    assert_eq!(Q::zero().pow_i32(0), Q::one());
    // i32::MIN must not overflow when negated.
    assert_total(two.pow_i32(i32::MIN), "pow_i32(i32::MIN)");

    let mut rng = Rng::new(0x5EED_0024);
    for _ in 0..5_000 {
        let q = Q::Number(rng.q());
        let e = (rng.below(21) as i32) - 10;
        assert_total(q.pow_i32(e), "pow_i32");
    }
}
