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

// ===========================================================================
// pi, sin, cos, tan, atan
// ===========================================================================

/// `atan(z)` over exact rationals, to 2^-90, for `|z| <= 1/2`.
fn oracle_atan_small(z: &Rational) -> Rational {
    let z2 = z.clone() * z.clone();
    let mut term = z.clone();
    let mut sum = z.clone();
    let tol = eps(90);
    for j in 1..400u32 {
        term *= z2.clone();
        let piece = term.clone() / Rational::from_signeds((2 * j + 1) as i128, 1i128);
        if j % 2 == 1 {
            sum -= piece.clone();
        } else {
            sum += piece.clone();
        }
        if mag(&piece) < tol {
            break;
        }
    }
    sum
}

/// `π` by Machin, at 2^-90.
fn oracle_pi() -> Rational {
    Rational::from_signeds(16i128, 1i128) * oracle_atan_small(&Rational::from_signeds(1i128, 5i128))
        - Rational::from_signeds(4i128, 1i128)
            * oracle_atan_small(&Rational::from_signeds(1i128, 239i128))
}

/// `sin(x)` (or `cos`) by direct Maclaurin over exact rationals, no reduction.
/// Only usable for modest `|x|`, which is exactly where it is used.
fn oracle_sin_cos(x: &Rational, want_cos: bool) -> Rational {
    let x2 = x.clone() * x.clone();
    let (mut term, mut sum) = if want_cos {
        (one(), one())
    } else {
        (x.clone(), x.clone())
    };
    let tol = eps(90);
    for k in 1..200u32 {
        let d = if want_cos {
            ((2 * k - 1) as i128) * ((2 * k) as i128)
        } else {
            ((2 * k) as i128) * ((2 * k + 1) as i128)
        };
        term = term * x2.clone() / Rational::from_signeds(d, 1i128);
        if k % 2 == 1 {
            sum -= term.clone();
        } else {
            sum += term.clone();
        }
        if mag(&term) < tol {
            break;
        }
    }
    sum
}

#[test]
fn pi_is_accurate() {
    let want = oracle_pi();
    match the_q::transcendental::pi() {
        Q::Number(r) => {
            let e = rel_err(&rat(r), &want);
            println!("pi: relative error 2^-{}", precision_bits(&e));
            assert!(e <= eps(55), "pi = {r} is not accurate enough");
        }
        other => panic!("pi must be a number, got {other}"),
    }
}

#[test]
fn atan_is_accurate_and_matches_known_points() {
    // atan(1) == pi/4 and atan(0) == 0 are the anchors.
    let quarter_pi = oracle_pi() / Rational::from_signeds(4i128, 1i128);
    if let Q::Number(r) = Q::one().atan() {
        assert!(
            rel_err(&rat(r), &quarter_pi) <= eps(45),
            "atan(1) = {r} should be pi/4"
        );
    } else {
        panic!("atan(1) must be a number");
    }
    assert_eq!(Q::zero().atan(), Q::zero(), "atan(0) is exactly 0");

    // Both infinities have exact limits, which is unusual here.
    if let Q::Number(r) = Q::PosInf.atan() {
        let half_pi = oracle_pi() / two_rational();
        assert!(rel_err(&rat(r), &half_pi) <= eps(45), "atan(+inf) = pi/2");
    } else {
        panic!("atan(+inf) must be a number");
    }
    assert_eq!(Q::PosSat.atan(), Q::Nan);
    assert_eq!(Q::Nan.atan(), Q::Nan);

    let mut rng = Rng::new(0x5EED_0030);
    let mut worst = oracle_zero();
    for _ in 0..2_000 {
        let x = rng.q();
        // The oracle series needs |z| <= 1/2, so check there directly and rely
        // on the reduction identities elsewhere (covered by tan/atan round trip).
        let half = Rational::from_signeds(1i128, 2i128);
        if mag(&rat(x)) > half {
            continue;
        }
        let want = oracle_atan_small(&rat(x));
        if let Q::Number(r) = Q::Number(x).atan() {
            let e = rel_err(&rat(r), &want);
            if e > worst {
                worst = e.clone();
            }
            assert!(e <= eps(45), "atan({x}) = {r}, want ~{want}");
        }
    }
    println!("atan: worst relative error 2^-{}", precision_bits(&worst));
}

#[test]
fn sin_and_cos_match_a_direct_series() {
    let mut rng = Rng::new(0x5EED_0031);
    let (mut ws, mut wc) = (oracle_zero(), oracle_zero());
    for _ in 0..2_000 {
        // Modest arguments, where a reduction-free oracle is tractable. The
        // reduction path itself is exercised by the identity tests below.
        let k = (rng.below(21) as i64) - 10;
        let frac = rng.q_unit();
        let q = Q::add(Q::Number(Rat::new(k, 1).unwrap()), Q::Number(frac));
        let Q::Number(xv) = q else { continue };
        let want_s = oracle_sin_cos(&rat(xv), false);
        let want_c = oracle_sin_cos(&rat(xv), true);
        if let Q::Number(r) = q.sin() {
            let e = rel_err(&rat(r), &want_s);
            if e > ws {
                ws = e.clone();
            }
            assert!(e <= eps(35), "sin({xv}) = {r}, want ~{want_s}");
        }
        if let Q::Number(r) = q.cos() {
            let e = rel_err(&rat(r), &want_c);
            if e > wc {
                wc = e.clone();
            }
            assert!(e <= eps(35), "cos({xv}) = {r}, want ~{want_c}");
        }
    }
    println!(
        "sin: worst relative error 2^-{}; cos: 2^-{}",
        precision_bits(&ws),
        precision_bits(&wc)
    );
}

#[test]
fn pythagorean_identity_holds() {
    // sin^2 + cos^2 == 1 across the whole accepted range, including where
    // argument reduction does the most work. This is what a shared reduction
    // between sin and cos buys.
    let mut rng = Rng::new(0x5EED_0032);
    let mut worst = oracle_zero();
    for _ in 0..5_000 {
        let k = (rng.below(2_000_000) as i64) - 1_000_000;
        let q = Q::Number(Rat::new(k, 1000).unwrap());
        let (s, c) = (q.sin(), q.cos());
        if let (Q::Number(sv), Q::Number(cv)) = (s, c) {
            let sum = rat(sv) * rat(sv) + rat(cv) * rat(cv);
            let e = mag(&(sum - one()));
            if e > worst {
                worst = e.clone();
            }
            assert!(e <= eps(30), "sin^2+cos^2 at {q} is off by {e}");
        }
    }
    println!(
        "sin^2 + cos^2 - 1: worst absolute error 2^-{}",
        precision_bits(&worst)
    );
}

#[test]
fn sin_and_cos_at_the_landmark_angles() {
    let pi = the_q::transcendental::pi();
    let half_pi = Q::div(pi, Q::new(2, 1));
    assert_eq!(Q::zero().sin(), Q::zero(), "sin(0) is exactly 0");
    assert_eq!(Q::zero().cos(), Q::one(), "cos(0) is exactly 1");
    // sin(pi/2) ~ 1, cos(pi/2) ~ 0, sin(pi) ~ 0, cos(pi) ~ -1.
    for (val, want, what) in [
        (half_pi.sin(), one(), "sin(pi/2)"),
        (pi.cos(), -one(), "cos(pi)"),
    ] {
        if let Q::Number(r) = val {
            assert!(
                mag(&(rat(r) - want)) <= eps(35),
                "{what} = {r} is off target"
            );
        } else {
            panic!("{what} must be a number");
        }
    }
    for (val, what) in [(half_pi.cos(), "cos(pi/2)"), (pi.sin(), "sin(pi)")] {
        if let Q::Number(r) = val {
            assert!(mag(&rat(r)) <= eps(35), "{what} = {r} should be ~0");
        } else {
            panic!("{what} must be a number");
        }
    }
}

#[test]
fn sin_and_cos_stay_within_minus_one_and_one() {
    let mut rng = Rng::new(0x5EED_0033);
    let slack = eps(30);
    for _ in 0..20_000 {
        let k = (rng.below(2_000_000) as i64) - 1_000_000;
        let q = Q::Number(Rat::new(k, 997).unwrap());
        for (v, what) in [(q.sin(), "sin"), (q.cos(), "cos")] {
            if let Q::Number(r) = v {
                assert!(
                    mag(&rat(r)) <= one() + slack.clone(),
                    "{what}({q}) = {r} escaped [-1, 1]"
                );
            }
        }
    }
}

#[test]
fn trig_refuses_arguments_it_cannot_reduce() {
    // Past 2^20 the reduction error swamps the answer, so a Nan is returned
    // rather than a plausible-looking number. f64 does the opposite.
    let big = Q::Number(Rat::new((1i64 << 20) + 1, 1).unwrap());
    assert_eq!(big.sin(), Q::Nan);
    assert_eq!(big.cos(), Q::Nan);
    assert_eq!(big.neg().sin(), Q::Nan);
    // Just inside the limit it still answers.
    let ok = Q::Number(Rat::new((1i64 << 20) - 1, 1).unwrap());
    assert!(ok.sin().is_number() && ok.cos().is_number());
    // No limit at infinity: a genuine non-answer, not a shortcoming.
    assert_eq!(Q::PosInf.sin(), Q::Nan);
    assert_eq!(Q::NegInf.cos(), Q::Nan);
    assert_eq!(Q::PosSat.sin(), Q::Nan);
}

#[test]
fn tan_matches_sin_over_cos_and_handles_its_poles() {
    let mut rng = Rng::new(0x5EED_0034);
    for _ in 0..5_000 {
        let k = (rng.below(20_000) as i64) - 10_000;
        let q = Q::Number(Rat::new(k, 1000).unwrap());
        assert_eq!(q.tan(), Q::div(q.sin(), q.cos()), "tan must be sin/cos");
        assert_total(q.tan(), "tan");
    }
    // Near a pole the quotient blows up rather than trapping, which is the
    // honest answer since tan genuinely has one there.
    let half_pi = Q::div(the_q::transcendental::pi(), Q::new(2, 1));
    assert_total(half_pi.tan(), "tan(pi/2)");
}

#[test]
fn atan_inverts_tan_on_the_principal_branch() {
    let mut rng = Rng::new(0x5EED_0035);
    for _ in 0..2_000 {
        // Stay well inside (-pi/2, pi/2), where atan(tan(x)) == x.
        let k = (rng.below(2_800) as i64) - 1_400;
        let x = Q::Number(Rat::new(k, 1000).unwrap());
        if let Q::Number(t) = x.tan() {
            if let Q::Number(back) = Q::Number(t).atan() {
                let d = mag(&(rat(back)
                    - rat(match x {
                        Q::Number(v) => v,
                        _ => unreachable!(),
                    })));
                assert!(d <= eps(25), "atan(tan({x})) = {back}, off by {d}");
            }
        }
    }
}

#[test]
fn trig_is_total_and_never_panics() {
    for q in states() {
        assert_total(q.sin(), "sin");
        assert_total(q.cos(), "cos");
        assert_total(q.tan(), "tan");
        assert_total(q.atan(), "atan");
    }
    let mut rng = Rng::new(0x5EED_0036);
    for _ in 0..20_000 {
        let n = rng.next_u64() as i64;
        let d = rng.next_u64() as i64;
        let q = Q::new(n, d);
        assert_total(q.sin(), "sin");
        assert_total(q.cos(), "cos");
        assert_total(q.tan(), "tan");
        assert_total(q.atan(), "atan");
    }
}

// ===========================================================================
// The pinned constants
//
// `pi`, `e` and `ln2` return literals rather than summing a series on every
// call — benchmarking showed the series dominating every function that used
// them. A hard-coded constant is only acceptable if it can be re-derived and
// is checked, so each of these asserts the literal is **bit-identical** to what
// its series produces. If the series, the width budget or the rounding
// contract ever changes, these fail rather than silently drifting.
// ===========================================================================

#[test]
fn pi_is_the_series_value() {
    assert_eq!(
        the_q::transcendental::pi(),
        the_q::transcendental::pi_series(),
        "the pi literal has drifted from its Machin derivation"
    );
}

#[test]
fn e_is_the_series_value() {
    assert_eq!(
        the_q::transcendental::e(),
        the_q::transcendental::e_series(),
        "the e literal has drifted from its factorial-series derivation"
    );
}

#[test]
fn ln2_is_the_series_value() {
    assert_eq!(
        the_q::transcendental::ln2(),
        the_q::transcendental::ln2_series(),
        "the ln2 literal has drifted from its atanh derivation"
    );
}

#[test]
fn e_is_accurate_and_consistent_with_exp_and_ln() {
    // Independently: e must match the oracle's exponential at 1...
    let want = oracle_exp(&one());
    match the_q::transcendental::e() {
        Q::Number(r) => {
            let err = rel_err(&rat(r), &want);
            println!("e: relative error 2^-{}", precision_bits(&err));
            assert!(err <= eps(55), "e = {r} is not accurate enough");
        }
        other => panic!("e must be a number, got {other}"),
    }
    // ...and ln(e) must come back to 1.
    if let Q::Number(r) = the_q::transcendental::e().ln() {
        assert!(
            mag(&(rat(r) - one())) <= eps(45),
            "ln(e) = {r}, should be 1"
        );
    } else {
        panic!("ln(e) must be a number");
    }
}

#[test]
fn ln10_is_the_series_value() {
    assert_eq!(
        the_q::transcendental::ln10(),
        the_q::transcendental::ln10_series(),
        "the ln10 literal has drifted from ln(10)"
    );
}

// ===========================================================================
// The rest of the standard function set
// ===========================================================================

#[test]
fn logarithms_in_other_bases_are_consistent() {
    let mut rng = Rng::new(0x5EED_0040);
    for _ in 0..2_000 {
        let x = rng.q();
        if x.numerator() <= 0 {
            continue;
        }
        let q = Q::Number(x);
        // log2(x)·ln2 == ln(x), and likewise for log10.
        if let (Q::Number(l2), Q::Number(ln)) = (q.log2(), q.ln()) {
            let lhs = rat(l2)
                * rat(match the_q::transcendental::ln2() {
                    Q::Number(v) => v,
                    _ => unreachable!(),
                });
            assert!(
                rel_err(&lhs, &rat(ln)) <= eps(40),
                "log2({x})·ln2 should equal ln({x})"
            );
        }
        if let (Q::Number(l10), Q::Number(ln)) = (q.log10(), q.ln()) {
            let lhs = rat(l10)
                * rat(match the_q::transcendental::ln10() {
                    Q::Number(v) => v,
                    _ => unreachable!(),
                });
            assert!(
                rel_err(&lhs, &rat(ln)) <= eps(40),
                "log10({x})·ln10 should equal ln({x})"
            );
        }
    }
    // Landmark values.
    for (n, want) in [(2i64, 1i64), (8, 3), (1024, 10)] {
        if let Q::Number(r) = Q::Number(Rat::new(n, 1).unwrap()).log2() {
            let d = mag(&(rat(r) - Rational::from_signeds(want as i128, 1i128)));
            assert!(d <= eps(35), "log2({n}) = {r}, want {want}");
        }
    }
    for (n, want) in [(10i64, 1i64), (1000, 3)] {
        if let Q::Number(r) = Q::Number(Rat::new(n, 1).unwrap()).log10() {
            let d = mag(&(rat(r) - Rational::from_signeds(want as i128, 1i128)));
            assert!(d <= eps(35), "log10({n}) = {r}, want {want}");
        }
    }
}

#[test]
fn exp2_and_powf_agree_with_integer_powers() {
    for k in 0i64..40 {
        if let Q::Number(r) = Q::Number(Rat::new(k, 1).unwrap()).exp2() {
            let want = Rational::from_signeds(1i128 << k, 1i128);
            assert!(
                rel_err(&rat(r), &want) <= eps(40),
                "exp2({k}) = {r}, want 2^{k}"
            );
        }
    }
    // powf against the exact integer power.
    let mut rng = Rng::new(0x5EED_0041);
    for _ in 0..1_000 {
        let base = rng.q_unit();
        if base.numerator() <= 0 {
            continue;
        }
        let e = 1 + (rng.below(5) as u32);
        let q = Q::Number(base);
        if let (Q::Number(a), Q::Number(b)) = (
            q.powf(Q::Number(Rat::new(e as i64, 1).unwrap())),
            q.pow_u32(e),
        ) {
            assert!(
                rel_err(&rat(a), &rat(b)) <= eps(30),
                "powf({base}, {e}) = {a} disagrees with pow_u32 = {b}"
            );
        }
    }
    // The conventions.
    assert_eq!(Q::zero().powf(Q::zero()), Q::one(), "0^0 is 1");
    assert_eq!(Q::zero().powf(Q::one()), Q::zero());
}

#[test]
fn cbrt_cubes_back_and_handles_negatives() {
    let mut rng = Rng::new(0x5EED_0042);
    for _ in 0..2_000 {
        let x = rng.q();
        if x.numerator() == 0 {
            continue;
        }
        let q = Q::Number(x);
        if let Q::Number(r) = q.cbrt() {
            let cube = rat(r) * rat(r) * rat(r);
            assert!(
                rel_err(&cube, &rat(x)) <= eps(30),
                "cbrt({x}) = {r}; cubing gives {cube}"
            );
        }
    }
    // Unlike sqrt, the whole real line is in the domain.
    if let Q::Number(r) = Q::Number(Rat::new(-8, 1).unwrap()).cbrt() {
        assert!(
            mag(&(rat(r) + Rational::from_signeds(2i128, 1i128))) <= eps(30),
            "cbrt(-8) = {r}, want -2"
        );
    } else {
        panic!("cbrt of a negative must be a number");
    }
    assert_eq!(Q::zero().cbrt(), Q::zero());
}

#[test]
fn hypot_avoids_the_overflow_the_naive_form_hits() {
    // The point of the identity: a² + b² can leave the budget when
    // sqrt(a² + b²) comfortably fits.
    let big = Q::Number(Rat::new(MAX_MAG / 2, 1).unwrap());
    let naive = Q::add(Q::mul(big, big), Q::mul(big, big));
    assert!(
        naive.is_saturated(),
        "premise: the naive form really does overflow here"
    );
    let h = big.hypot(big);
    assert!(
        h.is_number(),
        "hypot must survive where a²+b² does not, got {h}"
    );

    // 3-4-5 and its scalings.
    for k in 1i64..1000 {
        let (a, b) = (
            Q::Number(Rat::new(3 * k, 1).unwrap()),
            Q::Number(Rat::new(4 * k, 1).unwrap()),
        );
        if let Q::Number(r) = a.hypot(b) {
            let want = Rational::from_signeds((5 * k) as i128, 1i128);
            assert!(
                rel_err(&rat(r), &want) <= eps(40),
                "hypot(3k, 4k) at k={k} = {r}, want {want}"
            );
        }
    }
    assert_eq!(Q::zero().hypot(Q::zero()), Q::zero());
}

#[test]
fn hyperbolics_satisfy_their_identity() {
    // cosh² - sinh² == 1.
    let mut rng = Rng::new(0x5EED_0043);
    let mut worst = oracle_zero();
    for _ in 0..2_000 {
        let k = (rng.below(2_000) as i64) - 1_000;
        let q = Q::Number(Rat::new(k, 100).unwrap());
        if let (Q::Number(s), Q::Number(c)) = (q.sinh(), q.cosh()) {
            let d = rat(c) * rat(c) - rat(s) * rat(s);
            let e = mag(&(d - one()));
            if e > worst {
                worst = e.clone();
            }
            assert!(e <= eps(30), "cosh²-sinh² at {q} is off by {e}");
        }
    }
    println!(
        "cosh^2 - sinh^2 - 1: worst absolute error 2^-{}",
        precision_bits(&worst)
    );
    assert_eq!(Q::zero().sinh(), Q::zero(), "sinh(0) is exactly 0");
    assert_eq!(Q::zero().cosh(), Q::one(), "cosh(0) is exactly 1");
    assert_eq!(Q::zero().tanh(), Q::zero());
}

#[test]
fn tanh_has_no_poles_and_stays_bounded() {
    // cosh is never zero, so unlike tan this never blows up.
    let mut rng = Rng::new(0x5EED_0044);
    for _ in 0..5_000 {
        let k = (rng.below(8_000) as i64) - 4_000;
        let q = Q::Number(Rat::new(k, 100).unwrap());
        let t = q.tanh();
        assert_total(t, "tanh");
        if let Q::Number(r) = t {
            assert!(
                mag(&rat(r)) <= one() + eps(30),
                "tanh({q}) = {r} escaped [-1, 1]"
            );
        }
    }
}

#[test]
fn asin_and_acos_invert_sin_and_cos() {
    let mut rng = Rng::new(0x5EED_0045);
    for _ in 0..2_000 {
        let x = rng.q_unit();
        let q = Q::Number(x);
        // sin(asin(x)) == x
        if let Q::Number(a) = q.asin() {
            if let Q::Number(back) = Q::Number(a).sin() {
                assert!(
                    rel_err(&rat(back), &rat(x)) <= eps(25),
                    "sin(asin({x})) = {back}"
                );
            }
        }
        // asin + acos == pi/2
        if let (Q::Number(a), Q::Number(c)) = (q.asin(), q.acos()) {
            let sum = rat(a) + rat(c);
            let half_pi = oracle_pi() / two_rational();
            assert!(
                rel_err(&sum, &half_pi) <= eps(30),
                "asin({x}) + acos({x}) should be pi/2"
            );
        }
    }
    // Endpoints and the domain boundary.
    let half_pi = oracle_pi() / two_rational();
    if let Q::Number(r) = Q::one().asin() {
        assert!(rel_err(&rat(r), &half_pi) <= eps(45), "asin(1) = pi/2");
    } else {
        panic!("asin(1) must be a number");
    }
    assert_eq!(Q::zero().asin(), Q::zero(), "asin(0) is exactly 0");
    assert_eq!(
        Q::Number(Rat::new(2, 1).unwrap()).asin(),
        Q::Nan,
        "no real arcsine outside [-1, 1]"
    );
    assert_eq!(Q::Number(Rat::new(-2, 1).unwrap()).asin(), Q::Nan);
}

#[test]
fn atan2_gets_the_quadrant_right() {
    // The whole reason atan2 exists: atan(y/x) cannot tell these apart.
    let p = oracle_pi();
    let one_q = Q::one();
    let neg_q = Q::neg_one();
    let cases = [
        (
            one_q,
            one_q,
            p.clone() / Rational::from_signeds(4i128, 1i128),
        ),
        (
            one_q,
            neg_q,
            Rational::from_signeds(3i128, 4i128) * p.clone(),
        ),
        (
            neg_q,
            neg_q,
            -Rational::from_signeds(3i128, 4i128) * p.clone(),
        ),
        (
            neg_q,
            one_q,
            -p.clone() / Rational::from_signeds(4i128, 1i128),
        ),
    ];
    for (y, x, want) in cases {
        match y.atan2(x) {
            Q::Number(r) => assert!(
                mag(&(rat(r) - want.clone())) <= eps(30),
                "atan2({y}, {x}) = {r}, want {want}"
            ),
            other => panic!("atan2({y}, {x}) = {other}"),
        }
    }
    // The origin has no angle; returning zero would invent one.
    assert_eq!(Q::zero().atan2(Q::zero()), Q::Nan);
    // On the axes.
    if let Q::Number(r) = Q::one().atan2(Q::zero()) {
        assert!(mag(&(rat(r) - p.clone() / two_rational())) <= eps(30));
    } else {
        panic!("atan2(1, 0) must be a number");
    }
}

#[test]
fn the_whole_function_set_is_total() {
    // Every function, every state, plus a wide random sweep. Nothing panics and
    // nothing returns a malformed or unclassified value.
    let mut rng = Rng::new(0x5EED_0046);
    let mut all: Vec<Q> = states();
    for _ in 0..2_000 {
        all.push(Q::new(rng.next_u64() as i64, rng.next_u64() as i64));
    }
    for q in all {
        for (v, what) in [
            (q.sqrt(), "sqrt"),
            (q.cbrt(), "cbrt"),
            (q.exp(), "exp"),
            (q.exp2(), "exp2"),
            (q.ln(), "ln"),
            (q.log2(), "log2"),
            (q.log10(), "log10"),
            (q.sin(), "sin"),
            (q.cos(), "cos"),
            (q.tan(), "tan"),
            (q.asin(), "asin"),
            (q.acos(), "acos"),
            (q.atan(), "atan"),
            (q.sinh(), "sinh"),
            (q.cosh(), "cosh"),
            (q.tanh(), "tanh"),
            (q.hypot(Q::one()), "hypot"),
            (q.atan2(Q::one()), "atan2"),
            (q.powf(Q::new(3, 2)), "powf"),
            (q.log(Q::new(3, 1)), "log"),
        ] {
            assert_total(v, what);
        }
    }
}
