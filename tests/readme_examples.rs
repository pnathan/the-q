//! The README's code examples. This file compiles and runs them.
//!
//! The crate does not include the README via `#![doc = include_str!(...)]`.
//! The README examples are therefore not doctests. Without this file, nothing
//! detects drift between those examples and the API. Each test below
//! reproduces one fenced block of `README.md` verbatim; the test name says
//! which section it comes from.

#![allow(clippy::eq_op)]

use std::collections::BTreeMap;
use std::str::FromStr;
use the_q::nary;
use the_q::transcendental;
use the_q::{Dir, Exact, ExactError, MAX_DEC_PLACES, MAX_MAG, ParseQError, Q, QI, Rat, Sign};
use the_q::{from_f64_dir, q_from_f64, to_f64};

// ---------------------------------------------------------------------------
// Opening example
// ---------------------------------------------------------------------------

#[test]
fn readme_opening() {
    let price = Rat::from_decimal(1999, 2).unwrap(); // 19.99, exactly
    let rate = Rat::from_decimal(825, 4).unwrap(); //  0.0825, exactly
    let tax = Rat::mul(price, rate); //  1.649175, exactly
    assert_eq!(tax.to_string(), "65967/40000");

    let third = Rat::new(1, 3).unwrap();
    assert_eq!(third + third + third, Rat::one()); // no drift

    // Division by zero is not a panic on `Q`; it is a value.
    assert_eq!(Q::new(1, 0), Q::PosInf);
    assert_eq!(Q::div(Q::zero(), Q::zero()), Q::Nan);
}

// ---------------------------------------------------------------------------
// Rat
// ---------------------------------------------------------------------------

#[test]
fn readme_rat_construct() {
    // Every constructor canonicalises: sign on the numerator, gcd removed.
    assert_eq!(Rat::new(6, 8), Rat::new(3, 4));
    assert_eq!(Rat::new(3, -6).unwrap().to_string(), "-1/2");
    assert_eq!(Rat::new(0, -7), Some(Rat::zero()));

    // `None` for a zero denominator, or a pair that does not fit the budget.
    assert_eq!(Rat::new(1, 0), None);
    assert_eq!(Rat::new(i64::MAX, 1), None);

    // Decimal literals are exact; `(1999, 2)` is 19.99.
    assert_eq!(Rat::from_decimal(1999, 2).unwrap().to_string(), "1999/100");
    assert_eq!(Rat::from_decimal(1, MAX_DEC_PLACES + 1), None);

    // `new_rounded` is total in the numerator: it rounds instead of refusing.
    let big = Rat::new_rounded(i64::MAX, 1, Dir::Down).unwrap();
    assert_eq!(big.numerator(), MAX_MAG);
    assert_eq!(Rat::new_rounded(1, 0, Dir::Down), None);

    assert_eq!(Rat::from_int(-5).unwrap(), Rat::new(-5, 1).unwrap());
}

#[test]
fn readme_rat_arith() {
    let a = Rat::new(1, 3).unwrap();
    let b = Rat::new(1, 6).unwrap();

    // Exact when the exact result fits, which is nearly always.
    assert_eq!(Rat::add(a, b), Rat::new(1, 2).unwrap());
    assert_eq!(a + b, Rat::new(1, 2).unwrap()); // operators delegate
    assert_eq!(a - b, Rat::new(1, 6).unwrap());
    assert_eq!(a * b, Rat::new(1, 18).unwrap());
    assert_eq!(-a, Rat::new(-1, 3).unwrap());
    assert_eq!(Rat::div(a, b), Rat::new(2, 1).unwrap());

    // No `/` operator on `Rat`: `div` has a precondition the operator cannot
    // express. Use `Rat::div`, `Rat::checked_div`, or move to `Q`.
    assert_eq!(Rat::checked_div(a, Rat::zero()), None);

    assert_eq!(a.recip(), Rat::new(3, 1).unwrap());
    assert_eq!(a.pow_u32(3), Rat::new(1, 27).unwrap());
    assert_eq!(Rat::new(-2, 5).unwrap().abs(), Rat::new(2, 5).unwrap());
}

#[test]
fn readme_rat_rounding() {
    // Reduced denominator of the sum is about 9.2e18, past the 2^62 budget.
    let a = Rat::new(1, 3_037_000_493).unwrap();
    let b = Rat::new(1, 3_037_000_499).unwrap();

    let nearest = Rat::add(a, b); // rounded, ties to even
    let down = Rat::add_dir(a, b, Dir::Down);
    let up = Rat::add_dir(a, b, Dir::Up);
    assert!(down <= nearest && nearest <= up); // R2: the exact sum lies in [down, up]
    assert!(down < up); // so rounding did happen

    // `checked_*` on `Rat` reports saturation only, not rounding.
    assert!(Rat::checked_add(a, b).is_some());
    let m = Rat::new(MAX_MAG, 1).unwrap();
    assert_eq!(Rat::checked_add(m, m), None); // over the budget
    assert_eq!(Rat::add(m, m), m); // the plain op saturates
}

#[test]
fn readme_rat_compare() {
    let a = Rat::new(1, 3).unwrap();
    let b = Rat::new(1, 2).unwrap();

    // Exact and total: cross-multiplication, never a float.
    assert!(a < b);
    assert_eq!(Rat::compare(a, b), -1);
    assert_eq!(Rat::min(a, b), a);
    assert_eq!(Rat::clamp(Rat::new(7, 1).unwrap(), a, b), b);

    // `Eq` and `Hash` are structural, and canonical form makes that value
    // equality, so `Rat` is a map key.
    let mut table = BTreeMap::new();
    table.insert(Rat::new(2, 4).unwrap(), "half");
    assert_eq!(table.get(&b), Some(&"half"));

    assert_eq!(Rat::new(-3, 4).unwrap().signum(), -1);
    assert!(Rat::new(3, 4).unwrap().in_unit_interval());
    assert!(Rat::zero().is_zero() && Rat::one().is_one());
}

#[test]
fn readme_rat_display() {
    let x = Rat::new(1, 3).unwrap();
    assert_eq!(x.to_string(), "1/3"); // always `num/den`, always canonical
    assert_eq!(x.numerator(), 1);
    assert_eq!(x.denominator(), 3);
    assert!((to_f64(x) - 0.333_333_333_333_333_3).abs() < 1e-15); // display only
}

// ---------------------------------------------------------------------------
// Q
// ---------------------------------------------------------------------------

#[test]
fn readme_q_total() {
    // Every `Rat` failure mode is a `Q` value.
    assert_eq!(Q::new(1, 0), Q::PosInf);
    assert_eq!(Q::new(-1, 0), Q::NegInf);
    assert_eq!(Q::new(0, 0), Q::Nan);
    assert_eq!(Q::new(6, 8), Q::Number(Rat::new(3, 4).unwrap()));

    assert_eq!(Q::div(Q::one(), Q::zero()), Q::PosInf);
    assert_eq!(Q::one() / Q::zero(), Q::PosInf); // `Q` has a `/` operator
    assert_eq!(Q::zero().recip(), Q::PosInf);

    // Overflow is reported as saturation, distinct from infinity.
    let m = Q::Number(Rat::new(MAX_MAG, 1).unwrap());
    let over = m + m;
    assert_eq!(over, Q::PosSat);
    assert!(over.is_saturated() && !over.is_infinite());
    assert_eq!(over.to_string(), ">max");

    // `checked_*` on `Q` returns `Option<Rat>`: `Some` only for a number.
    assert_eq!(Q::checked_add(m, m), None);
    assert_eq!(Q::checked_div(Q::one(), Q::zero()), None);
    assert_eq!(Q::checked_mul(Q::one(), Q::one()), Some(Rat::one()));
}

#[test]
fn readme_q_semantics() {
    // Saturation denotes a finite real, so this is exact where `0 * inf` is not.
    assert_eq!(Q::mul(Q::zero(), Q::PosSat), Q::zero());
    assert_eq!(Q::mul(Q::zero(), Q::PosInf), Q::Nan);
    assert_eq!(Q::PosInf - Q::PosInf, Q::Nan);
    assert_eq!(Q::PosSat.abs(), Q::PosSat);
    assert_eq!(-Q::NegSat, Q::PosSat);

    // The order is total and `Nan == Nan`, so `Q` is a map key too.
    let mut v = vec![Q::Nan, Q::PosInf, Q::zero(), Q::NegSat, Q::NegInf];
    v.sort();
    assert_eq!(v, vec![Q::NegInf, Q::NegSat, Q::zero(), Q::PosInf, Q::Nan]);

    // Selection propagates `Nan`; `Ord::min` cannot, so do not fold with it.
    assert_eq!(Q::min(Q::Nan, Q::one()), Q::Nan);
    assert_eq!([Q::Nan, Q::one()].into_iter().min(), Some(Q::one()));

    // Every non-`Nan` value has a sign.
    assert_eq!(Q::PosSat.signum(), Some(Sign::Positive));
    assert_eq!(Q::zero().signum(), Some(Sign::Zero));
    assert_eq!(Q::Nan.signum(), None);
}

#[test]
fn readme_q_folds() {
    let third = Q::new(1, 3);
    assert_eq!(Q::sum(&[third, third, third]), Q::one());
    assert_eq!(Q::product(&[Q::new(2, 1), Q::new(1, 4)]), Q::new(1, 2));

    // `(weight, value)` pairs. Total: a zero weight sum is `Nan` or `±Inf`.
    let mean = Q::weighted_mean(&[(Q::new(1, 2), Q::one()), (Q::new(1, 2), Q::zero())]);
    assert_eq!(mean, Q::new(1, 2));
    assert_eq!(Q::weighted_mean(&[]), Q::Nan);

    // A `Nan` anywhere in the fold is a `Nan` result.
    assert_eq!(Q::sum(&[Q::one(), Q::Nan]), Q::Nan);
}

#[test]
fn readme_q_text() {
    // `Display` and `FromStr` round-trip every state.
    for q in [
        Q::new(-3, 4),
        Q::PosSat,
        Q::NegSat,
        Q::PosInf,
        Q::NegInf,
        Q::Nan,
    ] {
        assert_eq!(Q::from_str(&q.to_string()), Ok(q));
    }
    assert_eq!(Q::Nan.to_string(), "nan");
    assert_eq!(Q::NegSat.to_string(), "<-max");

    // Input is canonicalised; a bare integer is accepted; a zero denominator
    // in *text* is a malformed numeral, not a computation.
    assert_eq!("2/4".parse::<Q>(), Ok(Q::new(1, 2)));
    assert_eq!("7".parse::<Q>(), Ok(Q::new(7, 1)));
    assert_eq!("1/0".parse::<Q>(), Err(ParseQError::ZeroDenominator));
    assert_eq!("0.5".parse::<Q>(), Err(ParseQError::Malformed));
}

// ---------------------------------------------------------------------------
// QI
// ---------------------------------------------------------------------------

#[test]
fn readme_qi() {
    let a = QI::new(Rat::new(1, 3).unwrap(), Rat::new(1, 2).unwrap()); // [1/3, 1/2]
    let b = QI::exact(Rat::new(3, 1).unwrap()); // [3, 3]

    // Endpoints round outward (`lo` down, `hi` up), so enclosure is proven:
    // if `x ∈ a` and `y ∈ b` then `x ∘ y ∈ a ∘ b` for `+`, `-`, `*`.
    let s = QI::add(a, b);
    assert_eq!(s.lower(), Rat::new(10, 3).unwrap());
    assert_eq!(s.upper(), Rat::new(7, 2).unwrap());
    assert!(s.contains(Rat::add(Rat::new(2, 5).unwrap(), Rat::new(3, 1).unwrap())));

    let p = QI::mul(a, QI::neg(b)); // sign patterns are all handled
    assert_eq!(p.lower(), Rat::new(-3, 2).unwrap());
    assert_eq!(p.upper(), Rat::new(-1, 1).unwrap());

    // `width` is rounded up and returned as a `Q`: `PosSat` if too wide.
    assert_eq!(a.width(), Q::new(1, 6));
    assert_eq!(a.checked_width(), Some(Rat::new(1, 6).unwrap()));
    let whole = QI::new(
        Rat::new(-MAX_MAG, 1).unwrap(),
        Rat::new(MAX_MAG, 1).unwrap(),
    );
    assert_eq!(whole.width(), Q::PosSat);
    assert_eq!(whole.checked_width(), None);

    // `hull` is the smallest interval containing both.
    assert_eq!(
        QI::hull(a, b),
        QI::new(Rat::new(1, 3).unwrap(), Rat::new(3, 1).unwrap())
    );

    // `lo > hi` is a precondition: `new` panics, `checked_new` is `None`.
    assert_eq!(QI::checked_new(Rat::one(), Rat::zero()), None);
}

// ---------------------------------------------------------------------------
// Exact
// ---------------------------------------------------------------------------

#[test]
fn readme_exact() {
    let half = Exact::new(Rat::new(1, 2).unwrap());
    assert_eq!(Exact::add(half, half).unwrap().value(), Rat::one());
    assert_eq!(
        Exact::mul(half, half).unwrap().value(),
        Rat::new(1, 4).unwrap()
    );

    // The same two operands `Rat::add` rounds above: here they are an error.
    let a = Exact::new(Rat::new(1, 3_037_000_493).unwrap());
    let b = Exact::new(Rat::new(1, 3_037_000_499).unwrap());
    assert_eq!(Exact::add(a, b), Err(ExactError::Inexact));
    assert_eq!(Exact::checked_add(a, b), None);
    assert!(Rat::checked_add(a.value(), b.value()).is_some()); // `Rat` only refuses saturation

    // Division by zero is a separate error, not a panic.
    assert_eq!(
        Exact::div(half, Exact::new(Rat::zero())),
        Err(ExactError::DivisionByZero)
    );
    assert_eq!(Exact::checked_div(half, Exact::new(Rat::zero())), None);

    // `Exact` has no `Ord`; compare with `Exact::le`.
    assert!(Exact::le(half, Exact::new(Rat::one())));
    assert!(half.is_nonneg());
}

// ---------------------------------------------------------------------------
// Transcendentals
// ---------------------------------------------------------------------------

#[test]
fn readme_transcendental() {
    // Exact where the answer is rational.
    assert_eq!(Q::new(4, 1).sqrt(), Q::new(2, 1));
    assert_eq!(Q::new(9, 4).sqrt(), Q::new(3, 2));
    assert_eq!(Q::zero().exp(), Q::one());
    assert_eq!(Q::one().ln(), Q::zero());
    assert_eq!(Q::new(2, 1).pow_i32(-3), Q::new(1, 8)); // a fold of `mul`

    // Otherwise a bounded rational near the true value; accuracy is measured,
    // not proven (see the table below).
    let Q::Number(pi) = transcendental::pi() else {
        panic!()
    };
    assert!((to_f64(pi) - std::f64::consts::PI).abs() < 1e-15);
    let Q::Number(e) = Q::one().exp() else {
        panic!()
    };
    assert!((to_f64(e) - std::f64::consts::E).abs() < 1e-15);
    // `log2(8)` is *not* exactly 3: `ln` is a series, and the quotient of two
    // rounded logarithms is a nearby rational, not the integer.
    let Q::Number(three) = Q::new(8, 1).log2() else {
        panic!()
    };
    assert_ne!(three, Rat::new(3, 1).unwrap());
    assert!((to_f64(three) - 3.0).abs() < 1e-15);

    // Total: every domain edge is a value, never a panic.
    assert_eq!(Q::new(-1, 1).sqrt(), Q::Nan);
    assert_eq!(Q::zero().ln(), Q::NegInf);
    assert_eq!(Q::new(50, 1).exp(), Q::PosSat); // above the budget
    assert_eq!(Q::new(-50, 1).exp(), Q::zero()); // below the grid
    assert_eq!(Q::PosSat.sqrt(), Q::Nan); // the image reaches back inside
    assert_eq!(Q::PosInf.atan(), transcendental::half_pi());
    assert_eq!(Q::Nan.sin(), Q::Nan);
}

// ---------------------------------------------------------------------------
// nary
// ---------------------------------------------------------------------------

#[test]
fn readme_nary() {
    let third = Rat::new(1, 3).unwrap();
    assert_eq!(nary::sum(&[third, third, third]), Rat::one());
    assert_eq!(nary::sum(&[]), Rat::zero());
    assert_eq!(
        nary::product(&[Rat::new(2, 3).unwrap(), Rat::new(3, 4).unwrap()]),
        Rat::new(1, 2).unwrap()
    );

    // `(weight, value)` pairs; `None` when the rounded weight sum is zero.
    let pairs = [
        (Rat::new(1, 4).unwrap(), Rat::one()),
        (Rat::new(3, 4).unwrap(), Rat::zero()),
    ];
    assert_eq!(nary::weighted_mean(&pairs), Some(Rat::new(1, 4).unwrap()));
    assert_eq!(nary::weighted_mean(&[]), None);
}

// ---------------------------------------------------------------------------
// Conversions
// ---------------------------------------------------------------------------

#[test]
fn readme_convert() {
    // `0.1f64` is not one tenth; the conversion is exact about the double.
    let tenth = from_f64_dir(0.1, Dir::Nearest).unwrap();
    assert_eq!(
        tenth,
        Rat::new(3_602_879_701_896_397, 36_028_797_018_963_968).unwrap()
    );
    assert_ne!(tenth, Rat::from_decimal(1, 1).unwrap());

    // Directed conversion brackets the double when it does not fit exactly.
    let lo = from_f64_dir(1e-300, Dir::Down).unwrap();
    let hi = from_f64_dir(1e-300, Dir::Up).unwrap();
    assert!(lo <= hi);

    // `None` for NaN, infinity, and magnitudes above 2^61.
    assert_eq!(from_f64_dir(f64::NAN, Dir::Nearest), None);
    assert_eq!(from_f64_dir(1e300, Dir::Nearest), None);

    // `q_from_f64` is total. There is no `Q -> f64`: nothing denotes `PosSat`.
    assert_eq!(q_from_f64(f64::INFINITY), Q::PosInf);
    assert_eq!(q_from_f64(f64::NAN), Q::Nan);
    assert_eq!(q_from_f64(1e300), Q::PosSat);
    assert_eq!(q_from_f64(0.5), Q::new(1, 2));

    // `to_f64` is for display; three roundings, do not feed it back in.
    assert_eq!(to_f64(Rat::new(1, 4).unwrap()), 0.25);
}

#[cfg(feature = "serde")]
#[test]
fn readme_serde() {
    // `Rat` is the exact `[num, den]` pair; `Q` specials are strings.
    let x = Rat::new(17, 20).unwrap();
    assert_eq!(serde_json::to_string(&x).unwrap(), "[17,20]");
    assert_eq!(serde_json::from_str::<Rat>("[17,20]").unwrap(), x);
    assert_eq!(serde_json::to_string(&Q::PosSat).unwrap(), "\">max\"");
    assert_eq!(serde_json::from_str::<Q>("\"nan\"").unwrap(), Q::Nan);

    // Decoding re-canonicalises and rejects a malformed pair.
    assert_eq!(
        serde_json::from_str::<Rat>("[6,8]").unwrap(),
        Rat::new(3, 4).unwrap()
    );
    assert!(serde_json::from_str::<Rat>("[1,0]").is_err());
}

// ---------------------------------------------------------------------------
// Claims the README states as facts about the kernel
// ---------------------------------------------------------------------------

#[test]
fn readme_claims_about_the_kernel_defects_hold() {
    let zero = Rat::new(0, 1).unwrap();
    let one = Rat::new(1, 1).unwrap();
    assert!(Rat::new(1, 0).is_none(), "Rat::new(_, 0) is None");
    assert!(std::panic::catch_unwind(|| Rat::div(one, zero)).is_err());
    assert!(std::panic::catch_unwind(|| zero.recip()).is_err());
    assert!(std::panic::catch_unwind(|| QI::new(one, zero)).is_err());
    assert_eq!(Rat::checked_div(one, zero), None);
    let m = Rat::new(MAX_MAG, 1).unwrap();
    assert_eq!(Rat::add(m, m).numerator(), MAX_MAG);
}

#[test]
fn readme_claims_about_the_extended_type_hold() {
    assert_eq!(Q::Nan, Q::Nan);
    assert!(!Q::PosSat.is_infinite() && !Q::PosInf.is_saturated());
    assert!(!Q::PosSat.is_number());
    assert_eq!(Q::default(), Q::zero());
}

// ---------------------------------------------------------------------------
// Drift check
// ---------------------------------------------------------------------------

/// Every fenced block in `README.md` whose info string is exactly `rust` must
/// appear verbatim, indented by four spaces, somewhere in this file. Blocks
/// that are illustration only (`rust,ignore`, `toml`, `text`, `sh`) are not
/// checked. A README edit that is not mirrored here fails this test.
#[test]
fn every_readme_rust_block_is_reproduced_here() {
    let readme = include_str!("../README.md");
    let this = include_str!("readme_examples.rs");
    let mut lines = readme.lines();
    let mut blocks = 0;
    while let Some(line) = lines.next() {
        if line.trim_end() != "```rust" {
            continue;
        }
        blocks += 1;
        let mut body = String::new();
        for l in lines.by_ref() {
            if l.starts_with("```") {
                break;
            }
            if !l.is_empty() {
                body.push_str("    ");
                body.push_str(l);
            }
            body.push('\n');
        }
        assert!(
            this.contains(&body),
            "README block #{blocks} is not reproduced verbatim in tests/readme_examples.rs:\n{body}"
        );
    }
    assert!(
        blocks >= 15,
        "expected the README's rust blocks, found {blocks}"
    );
}
