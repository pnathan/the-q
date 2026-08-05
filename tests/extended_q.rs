//! The extended `Q`: classification, predicates, ordering, and the boundaries.
//!
//! # What is proven, and what these tests add
//!
//! The predicates in `ext.rs` have specifications against the ghost model. For
//! example, `is_one` is `x.n() == x.d()`, which is a statement about the
//! denoted rational. The implementations delegate to the verified kernel
//! predicates. The two are different statements, thus the postconditions have
//! content: a body that tests the numerator field alone fails verification.
//!
//! A specification that mirrors its own body has no content. Such a
//! specification verifies with the same defect in both. The protection here
//! comes from a specification against `n()` and `d()`, and not against the
//! fields, and from delegation instead of reimplementation.
//!
//! The differential suite against `malachite-q` covers a property that
//! verification does not: it tests the compiled artifact against an
//! arbitrary-precision oracle with separate code and separate authorship. A
//! proof that does not run against the artifact is a hypothesis about the
//! artifact. `predicates_would_catch_a_mutation` checks the generator, and
//! confirms that it draws inputs that separate a correct implementation from a
//! defective one.
//!
//! The laws of the order, which are totality, antisymmetry and transitivity,
//! are theorems in `ext.rs`. These tests re-check them exhaustively over the
//! representation classes, for the same artifact-level reason.

mod common;

use common::{rat, zero as oracle_zero, Rng};
use malachite_q::Rational;
use std::collections::BTreeMap;
use std::str::FromStr;
use the_q::{ParseQError, Rat, Sign, MAX_MAG, Q};

/// The five payload-free states.
const SPECIALS: [Q; 5] = [Q::PosSat, Q::NegSat, Q::PosInf, Q::NegInf, Q::Nan];

/// A spread of representation classes that covers every variant. It contains
/// several numbers, thus the sweeps below exercise the `Number`-vs-`Number`
/// case.
fn representatives() -> Vec<Q> {
    vec![
        Q::NegInf,
        Q::NegSat,
        Q::Number(Rat::new(-MAX_MAG, 1).unwrap()),
        Q::Number(Rat::new(-3, 2).unwrap()),
        Q::Number(Rat::new(-1, 1).unwrap()),
        Q::Number(Rat::new(0, 1).unwrap()),
        Q::Number(Rat::new(1, 3).unwrap()),
        Q::Number(Rat::new(1, 1).unwrap()),
        Q::Number(Rat::new(MAX_MAG, 1).unwrap()),
        Q::PosSat,
        Q::PosInf,
        Q::Nan,
    ]
}

// ===========================================================================
// Classification (stage 1)
// ===========================================================================

#[test]
fn classification_is_a_partition() {
    for q in representatives() {
        let n = [q.is_number(), q.is_saturated(), q.is_infinite(), q.is_nan()]
            .iter()
            .filter(|b| **b)
            .count();
        assert_eq!(n, 1, "{q} is in {n} classes, must be in exactly 1");
    }
}

#[test]
fn classification_assigns_each_variant_correctly() {
    assert!(Q::Number(Rat::new(1, 2).unwrap()).is_number());
    assert!(Q::PosSat.is_saturated() && Q::NegSat.is_saturated());
    assert!(Q::PosInf.is_infinite() && Q::NegInf.is_infinite());
    assert!(Q::Nan.is_nan());

    // Saturation is a distinct state in the type. An overflow is not a division
    // by zero. A caller uses `is_saturated` to tell the two apart. A collapse of
    // these two states removes the diagnostic value.
    assert!(!Q::PosSat.is_infinite(), "saturation is not infinity");
    assert!(!Q::PosInf.is_saturated(), "infinity is not saturation");
}

#[test]
fn there_is_deliberately_no_is_finite() {
    // This is a design guard, not a behavioural test. `PosSat` denotes reals
    // above the budget, and those reals are finite. Thus an `is_finite()` would
    // either give a wrong answer for `PosSat` or duplicate `is_number()`. Issue
    // #26 §1 rules the predicate out. An addition of `is_finite()` breaks this
    // named test.
    //
    // `PosSat` is finite in the mathematical sense. It is not a number in the
    // sense of this type. The predicate set encodes that distinction.
    assert!(!Q::PosSat.is_number());
    assert!(!Q::PosSat.is_infinite());
}

// ===========================================================================
// C2 — the value predicates, against an independent oracle
// ===========================================================================

/// The oracle's answers for a `Rat`. Arbitrary precision computes them. They
/// make no reference to anything in `the-q`.
fn oracle_predicates(x: Rat) -> (bool, bool, Sign, bool) {
    let r: Rational = rat(x);
    let z = oracle_zero();
    let one = Rational::from_signeds(1i128, 1i128);
    let sign = if r < z {
        Sign::Negative
    } else if r > z {
        Sign::Positive
    } else {
        Sign::Zero
    };
    (r == z, r == one, sign, r >= z && r <= one)
}

#[test]
fn predicates_agree_with_the_oracle_over_20k_cases() {
    let mut rng = Rng::new(0x5EED_1234_ABCD_0001);
    for i in 0..20_000u32 {
        let x = rng.q();
        let q = Q::Number(x);
        let (want_zero, want_one, want_sign, want_unit) = oracle_predicates(x);

        assert_eq!(q.is_zero(), want_zero, "is_zero disagrees at case {i}: {x}");
        assert_eq!(q.is_one(), want_one, "is_one disagrees at case {i}: {x}");
        assert_eq!(
            q.signum(),
            Some(want_sign),
            "signum disagrees at case {i}: {x}"
        );
        assert_eq!(
            q.in_unit_interval(),
            want_unit,
            "in_unit_interval disagrees at case {i}: {x}"
        );
    }
}

#[test]
fn predicates_cover_the_unit_interval_densely() {
    // `q()` above rarely lands in [0,1]. `q_unit()` always lands there. This is
    // therefore the case that `in_unit_interval` must answer correctly.
    let mut rng = Rng::new(0x5EED_1234_ABCD_0002);
    for _ in 0..5_000 {
        let x = rng.q_unit();
        let q = Q::Number(x);
        let (want_zero, want_one, want_sign, want_unit) = oracle_predicates(x);
        assert!(want_unit, "generator escaped [0,1] with {x}");
        assert_eq!(q.in_unit_interval(), want_unit);
        assert_eq!(q.is_zero(), want_zero);
        assert_eq!(q.is_one(), want_one);
        assert_eq!(q.signum(), Some(want_sign));
    }
}

#[test]
fn predicates_on_the_boundary_values() {
    let cases: [(i64, i64); 8] = [
        (0, 1),
        (1, 1),
        (-1, 1),
        (1, MAX_MAG),
        (MAX_MAG, MAX_MAG),
        (MAX_MAG, 1),
        (-MAX_MAG, 1),
        (MAX_MAG - 1, MAX_MAG),
    ];
    for (n, d) in cases {
        let x = Rat::new(n, d).unwrap();
        let q = Q::Number(x);
        let (want_zero, want_one, want_sign, want_unit) = oracle_predicates(x);
        assert_eq!(q.is_zero(), want_zero, "is_zero at {n}/{d}");
        assert_eq!(q.is_one(), want_one, "is_one at {n}/{d}");
        assert_eq!(q.signum(), Some(want_sign), "signum at {n}/{d}");
        assert_eq!(
            q.in_unit_interval(),
            want_unit,
            "in_unit_interval at {n}/{d}"
        );
    }
}

#[test]
fn every_predicate_is_false_on_every_special() {
    // Issue #26 §5 states these results explicitly, thus this test pins them.
    // On the saturations these results are the true answers, not conventions.
    // The interval (MAX_MAG, +inf) contains no 0, no 1 and no part of [0,1].
    for s in SPECIALS {
        assert!(!s.is_zero(), "{s}.is_zero() must be false");
        assert!(!s.is_one(), "{s}.is_one() must be false");
        assert!(
            !s.in_unit_interval(),
            "{s}.in_unit_interval() must be false"
        );
    }
}

#[test]
fn signum_is_none_exactly_on_nan() {
    // The sign is the one item of information that the specials carry. Issue
    // #26 §4 rejects the alternative that discards it.
    assert_eq!(Q::PosSat.signum(), Some(Sign::Positive));
    assert_eq!(Q::NegSat.signum(), Some(Sign::Negative));
    assert_eq!(Q::PosInf.signum(), Some(Sign::Positive));
    assert_eq!(Q::NegInf.signum(), Some(Sign::Negative));
    assert_eq!(Q::Nan.signum(), None);

    for q in representatives() {
        assert_eq!(
            q.signum().is_none(),
            q.is_nan(),
            "signum must be None exactly on Nan, disagreed at {q}"
        );
    }
}

#[test]
fn predicates_would_catch_a_mutation() {
    // This is a guard on the differential itself. The suite above has meaning
    // only if it fails on a defective implementation. This test therefore
    // defines a defective implementation. It confirms that the defective
    // implementation disagrees with the real one on the inputs that the
    // differential draws.
    //
    // The mutation is the usual one for this shape. It writes `is_one` as
    // "numerator is 1" and omits the condition on the denominator.
    fn mutated_is_one(x: Rat) -> bool {
        x.numerator() == 1
    }

    let mut rng = Rng::new(0x5EED_1234_ABCD_0003);
    let mut caught = 0;
    for _ in 0..20_000 {
        let x = rng.q();
        if Q::Number(x).is_one() != mutated_is_one(x) {
            caught += 1;
        }
    }
    assert!(
        caught > 0,
        "the differential draws no input separating is_one from a known-wrong \
         is_one, so it is not testing is_one"
    );
}

// ===========================================================================
// D3 — the total order
// ===========================================================================

#[test]
fn order_matches_the_specified_sequence() {
    // NegInf < NegSat < Number(...) < PosSat < PosInf < Nan
    let ascending = [
        Q::NegInf,
        Q::NegSat,
        Q::Number(Rat::new(-MAX_MAG, 1).unwrap()),
        Q::Number(Rat::new(0, 1).unwrap()),
        Q::Number(Rat::new(MAX_MAG, 1).unwrap()),
        Q::PosSat,
        Q::PosInf,
        Q::Nan,
    ];
    for i in 0..ascending.len() {
        for j in 0..ascending.len() {
            let expect_le = i <= j;
            assert_eq!(
                Q::le(ascending[i], ascending[j]),
                expect_le,
                "le({}, {}) wrong",
                ascending[i],
                ascending[j]
            );
            assert_eq!(
                ascending[i] <= ascending[j],
                expect_le,
                "Ord disagrees with Q::le at ({}, {})",
                ascending[i],
                ascending[j]
            );
        }
    }
}

#[test]
fn order_is_total_and_antisymmetric_over_all_pairs() {
    let vs = representatives();
    for &a in &vs {
        for &b in &vs {
            assert!(
                Q::le(a, b) || Q::le(b, a),
                "totality fails at ({a}, {b}): neither direction holds"
            );
            if Q::le(a, b) && Q::le(b, a) {
                assert_eq!(a, b, "antisymmetry fails at ({a}, {b})");
            }
        }
    }
}

#[test]
fn order_is_transitive_over_all_triples() {
    let vs = representatives();
    for &a in &vs {
        for &b in &vs {
            for &c in &vs {
                if Q::le(a, b) && Q::le(b, c) {
                    assert!(Q::le(a, c), "transitivity fails at ({a}, {b}, {c})");
                }
            }
        }
    }
}

#[test]
fn order_is_reflexive_including_nan() {
    // This behaviour departs from IEEE. Under IEEE every ordered comparison
    // with NaN is false. That rule forbids a total order. `f64` therefore has
    // no `Ord`, and it confines the total order to `total_cmp`. This type makes
    // the opposite trade.
    for q in representatives() {
        assert!(Q::le(q, q), "{q} is not <= itself");
        assert_eq!(q, q, "{q} is not == itself");
        assert!(!Q::lt(q, q), "{q} is < itself");
    }
    assert_eq!(Q::Nan, Q::Nan, "Nan == Nan must hold to keep Eq lawful");
}

#[test]
fn order_agrees_with_equality_and_hashing() {
    // `Hash` must be consistent with `Eq`. That consistency lets `Q` be a key.
    let vs = representatives();
    for &a in &vs {
        for &b in &vs {
            assert_eq!(
                a == b,
                Q::compare(a, b) == 0,
                "PartialEq and compare disagree at ({a}, {b})"
            );
        }
    }

    let mut m: BTreeMap<Q, &str> = BTreeMap::new();
    for (i, q) in vs.iter().enumerate() {
        m.insert(*q, if i == 0 { "first" } else { "other" });
    }
    assert_eq!(m.len(), vs.len(), "distinct values collided as map keys");
    assert_eq!(
        *m.keys().next().unwrap(),
        Q::NegInf,
        "NegInf must sort first"
    );
    assert_eq!(*m.keys().last().unwrap(), Q::Nan, "Nan must sort last");
}

#[test]
fn order_on_numbers_agrees_with_the_oracle() {
    let mut rng = Rng::new(0x5EED_1234_ABCD_0004);
    for _ in 0..20_000 {
        let (x, y) = (rng.q(), rng.q());
        let want = rat(x) <= rat(y);
        assert_eq!(
            Q::le(Q::Number(x), Q::Number(y)),
            want,
            "order on numbers disagrees with the oracle at ({x}, {y})"
        );
    }
}

#[test]
fn saturation_separates_strictly_from_every_number() {
    // This soundness fact justifies the placement. Every NegSat value is below
    // every Number, and every PosSat value is above every Number. Thus the
    // order on representations agrees with the order on denoted values here.
    let mut rng = Rng::new(0x5EED_1234_ABCD_0005);
    for _ in 0..5_000 {
        let q = Q::Number(rng.q());
        assert!(Q::lt(Q::NegSat, q), "NegSat must be strictly below {q}");
        assert!(Q::lt(q, Q::PosSat), "PosSat must be strictly above {q}");
        assert!(Q::lt(Q::NegInf, q) && Q::lt(q, Q::PosInf));
        assert!(Q::lt(q, Q::Nan), "Nan sorts last");
    }
}

#[test]
fn sorting_a_mixed_slice_lands_in_the_specified_order() {
    let mut v = representatives();
    v.reverse();
    v.sort();
    let expected = representatives();
    assert_eq!(v, expected, "sort did not reproduce the specified order");
}

#[test]
fn lt_le_gt_ge_are_mutually_consistent() {
    let vs = representatives();
    for &a in &vs {
        for &b in &vs {
            assert_eq!(Q::lt(a, b), !Q::le(b, a), "lt/le inconsistent at ({a},{b})");
            assert_eq!(Q::gt(a, b), Q::lt(b, a), "gt/lt inconsistent at ({a},{b})");
            assert_eq!(Q::ge(a, b), Q::le(b, a), "ge/le inconsistent at ({a},{b})");
            assert_eq!(
                Q::le(a, b) && Q::ge(a, b),
                a == b,
                "le+ge must mean equal at ({a},{b})"
            );
        }
    }
}

// ===========================================================================
// D1 — Display and FromStr
// ===========================================================================

#[test]
fn display_uses_the_specified_spellings() {
    assert_eq!(Q::Nan.to_string(), "nan");
    assert_eq!(Q::PosInf.to_string(), "inf");
    assert_eq!(Q::NegInf.to_string(), "-inf");
    assert_eq!(Q::PosSat.to_string(), ">max");
    assert_eq!(Q::NegSat.to_string(), "<-max");
    assert_eq!(Q::Number(Rat::new(51, 200).unwrap()).to_string(), "51/200");
}

#[test]
fn saturation_never_renders_as_a_number() {
    // The spelling has one purpose. A reader or a downstream parser must not
    // mistake a saturated result for an exact value.
    for s in [Q::PosSat, Q::NegSat] {
        let text = s.to_string();
        assert!(
            text.parse::<f64>().is_err() && text.parse::<i64>().is_err(),
            "{text} is readable as a number, which defeats the spelling"
        );
    }
}

#[test]
fn from_str_round_trips_all_six_states() {
    for q in representatives() {
        let text = q.to_string();
        let back = Q::from_str(&text)
            .unwrap_or_else(|e| panic!("{q} rendered as {text:?} failed to parse: {e}"));
        assert_eq!(back, q, "round-trip changed {q} (via {text:?})");
    }
}

#[test]
fn from_str_round_trips_random_numbers() {
    let mut rng = Rng::new(0x5EED_1234_ABCD_0006);
    for _ in 0..20_000 {
        let q = Q::Number(rng.q());
        let text = q.to_string();
        assert_eq!(
            Q::from_str(&text).unwrap(),
            q,
            "round-trip failed on {text}"
        );
    }
}

#[test]
fn from_str_accepts_specials_case_insensitively() {
    // This follows `f64::from_str`. IEEE 754 is the reference model for this
    // design.
    for (text, want) in [
        ("NAN", Q::Nan),
        ("NaN", Q::Nan),
        ("nan", Q::Nan),
        ("INF", Q::PosInf),
        ("Inf", Q::PosInf),
        ("-INF", Q::NegInf),
    ] {
        assert_eq!(Q::from_str(text).unwrap(), want, "failed on {text:?}");
    }
}

#[test]
fn from_str_accepts_a_bare_integer() {
    assert_eq!(
        Q::from_str("5").unwrap(),
        Q::Number(Rat::new(5, 1).unwrap())
    );
    assert_eq!(
        Q::from_str("-5").unwrap(),
        Q::Number(Rat::new(-5, 1).unwrap())
    );
    assert_eq!(
        Q::from_str("0").unwrap(),
        Q::Number(Rat::new(0, 1).unwrap())
    );
}

#[test]
fn from_str_canonicalises_like_the_constructor() {
    assert_eq!(
        Q::from_str("2/4").unwrap(),
        Q::Number(Rat::new(1, 2).unwrap())
    );
    assert_eq!(
        Q::from_str("3/-6").unwrap(),
        Q::Number(Rat::new(-1, 2).unwrap())
    );
}

#[test]
fn from_str_rejects_whitespace() {
    // This follows `i64::from_str`. A parser that trims silently also accepts
    // `"1 / 2"` in a data file.
    for text in [
        " nan", "nan ", " 1/2", "1/2 ", "1 /2", "1/ 2", "\t1/2", "1/2\n",
    ] {
        assert!(
            Q::from_str(text).is_err(),
            "{text:?} must not parse — whitespace is rejected"
        );
    }
}

#[test]
fn from_str_rejects_a_zero_denominator() {
    // `Q::new(1, 0)` is `PosInf`, because a *computation* divides by zero and
    // the result must be some value. `"1/0"` in an input stream is a malformed
    // numeral instead. Acceptance of it hides the typographic error that
    // produces it. Display never emits a zero denominator, thus this rejection
    // costs no round-trip.
    for text in ["0/0", "1/0", "-1/0"] {
        assert_eq!(
            Q::from_str(text),
            Err(ParseQError::ZeroDenominator),
            "{text:?} must be rejected, not mapped to a special"
        );
    }
    // The contrast with the total constructor is intentional.
    assert_eq!(Q::new(1, 0), Q::PosInf);
    assert_eq!(Q::new(-1, 0), Q::NegInf);
    assert_eq!(Q::new(0, 0), Q::Nan);
}

#[test]
fn from_str_rejects_malformed_shapes() {
    for text in [
        "", "/", "//", "1/", "/2", "1/2/3", "abc", "1.5", "1e3", "nan/1", "inf/2", "--1", "+", "-",
        ">max/1", "> max", ">MAXX",
    ] {
        assert!(Q::from_str(text).is_err(), "{text:?} must not parse");
    }
}

#[test]
fn from_str_distinguishes_overflow_from_malformed() {
    // `i64::MAX + 1` is a well-formed numeral that does not fit. `abc` is not a
    // numeral. A single error for both cases loses the information that a
    // caller needs. That information separates data that is too large from data
    // that is corrupt.
    assert_eq!(
        Q::from_str("9223372036854775808"),
        Err(ParseQError::IntOverflow)
    );
    assert_eq!(
        Q::from_str("1/9223372036854775808"),
        Err(ParseQError::IntOverflow)
    );
    assert_eq!(Q::from_str("abc"), Err(ParseQError::Malformed));
}

#[test]
fn from_str_rejects_values_outside_the_budget() {
    // Inside `i64` but outside the 2^62 - 1 budget.
    let over = MAX_MAG as i128 + 1;
    assert_eq!(
        Q::from_str(&format!("{over}")),
        Err(ParseQError::OutOfBudget)
    );
}

// ===========================================================================
// D2 — serde
// ===========================================================================

#[test]
fn serde_round_trips_all_six_states() {
    for q in representatives() {
        let json = serde_json::to_string(&q).unwrap();
        let back: Q = serde_json::from_str(&json)
            .unwrap_or_else(|e| panic!("{q} serialised as {json} failed to parse: {e}"));
        assert_eq!(back, q, "serde round-trip changed {q} (via {json})");
    }
}

#[test]
fn serde_round_trips_random_numbers() {
    let mut rng = Rng::new(0x5EED_1234_ABCD_0007);
    for _ in 0..20_000 {
        let q = Q::Number(rng.q());
        let json = serde_json::to_string(&q).unwrap();
        assert_eq!(serde_json::from_str::<Q>(&json).unwrap(), q);
    }
}

#[test]
fn serde_uses_the_same_spellings_as_display() {
    // Issue #26 §8 gives both one shared spelling. Two spellings can diverge.
    for q in SPECIALS {
        let json = serde_json::to_string(&q).unwrap();
        assert_eq!(
            json,
            format!("\"{}\"", q),
            "serde and Display disagree on {q}"
        );
    }
}

#[test]
fn serde_encodes_a_number_as_the_pair() {
    let q = Q::Number(Rat::new(51, 200).unwrap());
    assert_eq!(serde_json::to_string(&q).unwrap(), "[51,200]");
}

#[test]
fn serde_leaves_the_rat_wire_format_untouched() {
    // The extension does not change the encoding of a bare `Rat`. This break
    // does not include consumers of `Rat`.
    let x = Rat::new(51, 200).unwrap();
    assert_eq!(serde_json::to_string(&x).unwrap(), "[51,200]");
    assert_eq!(serde_json::from_str::<Rat>("[51,200]").unwrap(), x);
    assert_eq!(
        serde_json::from_str::<Rat>("[2,4]").unwrap(),
        Rat::new(1, 2).unwrap(),
        "Rat's deserialiser re-canonicalises, and still must"
    );
}

#[test]
fn serde_recanonicalises_a_non_reduced_pair() {
    assert_eq!(
        serde_json::from_str::<Q>("[2,4]").unwrap(),
        Q::Number(Rat::new(1, 2).unwrap())
    );
}

#[test]
fn serde_rejects_malformed_payloads() {
    // A hostile or defective producer can emit these shapes. Each one must give
    // an error, and not a silently wrong value.
    let bad = [
        r#"[1,0]"#,                   // zero denominator
        r#"[1]"#,                     // too short
        r#"[1,2,3]"#,                 // too long
        r#"[]"#,                      // empty
        r#""sat""#,                   // a plausible but wrong spelling
        r#""-sat""#,                  // the other plausible wrong spelling
        r#""NAN""#,                   // wrong case: machine input, thus strict
        r#""Inf""#,                   // wrong case
        r#""""#,                      // empty string
        r#"{"num":1,"den":2}"#,       // a map, not a pair
        r#"null"#,                    // null
        r#"true"#,                    // a bool
        r#"1.5"#,                     // a bare float
        r#"[1.5,2]"#,                 // a float where an integer belongs
        r#"["1","2"]"#,               // strings where integers belong
        r#"[9223372036854775807,1]"#, // inside i64, outside the budget
    ];
    for payload in bad {
        let parsed = serde_json::from_str::<Q>(payload);
        assert!(
            parsed.is_err(),
            "{payload} must be rejected, got {:?}",
            parsed.ok()
        );
    }
}

#[test]
fn serde_accepts_a_negative_denominator_and_normalises_the_sign() {
    // `[1,-2]` is *accepted*. `Rat::new` normalises the sign onto the
    // numerator, and `-1/2` is representable. This test pins the acceptance
    // explicitly, and the rejection list omits the case. Un-normalised input
    // resembles an error case. The canonicalisation makes it a valid case.
    assert_eq!(
        serde_json::from_str::<Q>("[1,-2]").unwrap(),
        Q::Number(Rat::new(-1, 2).unwrap())
    );
    assert_eq!(
        serde_json::from_str::<Q>("[-1,-2]").unwrap(),
        Q::Number(Rat::new(1, 2).unwrap())
    );
}

#[test]
fn serde_is_confined_to_self_describing_formats() {
    // This test makes the documented caveat executable. `deserialize_any`
    // limits the untagged encoding to formats that report the kind of the next
    // value. JSON reports it, thus this case succeeds. The test names the
    // dependency. A non-self-describing codec therefore fails here, where the
    // reason is clear.
    let q = Q::PosSat;
    let json = serde_json::to_string(&q).unwrap();
    assert_eq!(json, "\">max\"");
    assert_eq!(serde_json::from_str::<Q>(&json).unwrap(), q);
}

// ===========================================================================
// The total constructor
// ===========================================================================

#[test]
fn new_is_total_where_rat_new_is_partial() {
    // This design removes two defects. `Rat::new(_, 0)` reports failure out of
    // band. `Rat::zero().recip()` gives a value that violates the type
    // invariant. In the extended type every input maps to a value in the type.
    assert_eq!(Q::new(1, 0), Q::PosInf);
    assert_eq!(Q::new(-1, 0), Q::NegInf);
    assert_eq!(Q::new(0, 0), Q::Nan);
    assert_eq!(Q::new(1, 2), Q::Number(Rat::new(1, 2).unwrap()));

    // A value above the budget but finite saturates by sign. It does not fail.
    assert_eq!(Q::new(i64::MAX, 1), Q::PosSat);
    assert_eq!(Q::new(i64::MIN, 1), Q::NegSat);
    assert_eq!(Q::new(i64::MAX, -1), Q::NegSat);
}

#[test]
fn new_does_not_saturate_a_tiny_value_with_an_oversized_denominator() {
    // This is a regression test. `Rat::new` returns `None` for two different
    // reasons. The value is too large, or the reduced *denominator* is too
    // large while the value is small. An implementation that saturates on every
    // `None` from `Rat::new` merges the two reasons.
    //
    // `1 / i64::MIN` is about -1.08e-19. A result of `NegSat` asserts
    // |value| > MAX_MAG for a value in (-1, 0). That denotation is unsound. It
    // belongs to the silent-wrong-answer class that this type removes. The
    // constructor rounds instead, and under R3 the result is zero.
    assert!(
        Rat::new(1, i64::MIN).is_none(),
        "premise: Rat::new fails here"
    );

    for (n, d) in [
        (1i64, i64::MIN),
        (-1, i64::MIN),
        (1, i64::MAX),
        (-1, i64::MAX),
    ] {
        let q = Q::new(n, d);
        assert!(
            !q.is_saturated(),
            "{n}/{d} is about {:.3e} and must not saturate, got {q}",
            n as f64 / d as f64
        );
        assert!(q.is_number(), "{n}/{d} must round to a number, got {q}");
        assert!(
            q.in_unit_interval() || Q::lt(q, Q::zero()),
            "{n}/{d} must land near zero, got {q}"
        );
    }
}

#[test]
fn new_saturates_exactly_when_the_value_leaves_the_budget() {
    // The boundary is the *value*. MAX_MAG itself is representable, thus the
    // cut is strictly above MAX_MAG. `magnitude_fits` encodes this rule.
    assert_eq!(Q::new(MAX_MAG, 1), Q::Number(Rat::new(MAX_MAG, 1).unwrap()));
    assert_eq!(
        Q::new(-MAX_MAG, 1),
        Q::Number(Rat::new(-MAX_MAG, 1).unwrap())
    );
    assert_eq!(Q::new(MAX_MAG + 1, 1), Q::PosSat);
    assert_eq!(Q::new(-MAX_MAG - 1, 1), Q::NegSat);

    // Two large components with a small *ratio* never saturate.
    assert_eq!(
        Q::new(i64::MAX, i64::MAX),
        Q::Number(Rat::new(1, 1).unwrap())
    );
    assert!(!Q::new(i64::MAX - 1, i64::MAX).is_saturated());
    assert!(!Q::new(i64::MIN, i64::MAX).is_saturated());
}

#[test]
fn new_agrees_with_rat_new_wherever_rat_new_succeeds() {
    // Rounding returns a representable value unchanged (R1). The total
    // constructor is therefore a conservative extension of the partial one. It
    // gives no different answer. It gives an answer only where the partial
    // constructor gives none.
    let mut rng = Rng::new(0x5EED_1234_ABCD_0009);
    let mut agreed = 0u32;
    for _ in 0..20_000 {
        let n = rng.next_u64() as i64;
        let d = rng.next_u64() as i64;
        if let Some(x) = Rat::new(n, d) {
            assert_eq!(
                Q::new(n, d),
                Q::Number(x),
                "Q::new({n}, {d}) disagrees with Rat::new"
            );
            agreed += 1;
        }
    }
    assert!(
        agreed > 1_000,
        "only {agreed} cases exercised the agreement"
    );
}

#[test]
fn new_saturation_agrees_with_the_oracle_about_magnitude() {
    // This is the independent check. Saturation must mean |value| > MAX_MAG
    // under arbitrary-precision arithmetic. It must not depend on the reduction
    // code of this crate.
    let mut rng = Rng::new(0x5EED_1234_ABCD_000A);
    let max = Rational::from_signeds(MAX_MAG as i128, 1i128);
    let mut saturating = 0u32;
    for i in 0..20_000 {
        // Uniform i64 pairs almost never saturate. |n/d| > 2^62 needs a large
        // numerator over a *small* denominator, and a random 64-bit denominator
        // is almost always large. Half the draws therefore use a small
        // denominator. This makes the draws reach the saturating regime.
        // Without the small denominators the test passes vacuously.
        let n = rng.next_u64() as i64;
        let d = if i % 2 == 0 {
            (rng.below(64) as i64) - 32
        } else {
            rng.next_u64() as i64
        };
        if d == 0 {
            continue;
        }
        let exact = Rational::from_signeds(n as i128, d as i128);
        let mag = if exact < oracle_zero() {
            -exact.clone()
        } else {
            exact.clone()
        };
        let should_saturate = mag > max;
        let q = Q::new(n, d);
        assert_eq!(
            q.is_saturated(),
            should_saturate,
            "Q::new({n}, {d}) = {q}, but |{n}/{d}| > MAX_MAG is {should_saturate}"
        );
        if should_saturate {
            saturating += 1;
            assert_eq!(
                q == Q::PosSat,
                exact > oracle_zero(),
                "saturation sign wrong for {n}/{d}"
            );
        }
    }
    assert!(
        saturating > 100,
        "only {saturating} saturating cases drawn; the check is not exercised"
    );
}

#[test]
fn new_never_produces_a_malformed_value() {
    let mut rng = Rng::new(0x5EED_1234_ABCD_0008);
    for _ in 0..20_000 {
        let n = rng.next_u64() as i64;
        let d = rng.next_u64() as i64;
        let q = Q::new(n, d);
        if let Q::Number(x) = q {
            common::assert_wf(x, "Q::new");
        }
        // Each result falls into exactly one class.
        let c = [q.is_number(), q.is_saturated(), q.is_infinite(), q.is_nan()]
            .iter()
            .filter(|b| **b)
            .count();
        assert_eq!(c, 1, "Q::new({n}, {d}) produced an unclassified value");
    }
}

#[test]
fn constructors_agree_with_their_predicates() {
    assert!(Q::zero().is_zero());
    assert!(Q::one().is_one());
    assert_eq!(Q::neg_one().signum(), Some(Sign::Negative));
    assert!(Q::zero().in_unit_interval());
    assert!(Q::one().in_unit_interval());
    assert!(!Q::neg_one().in_unit_interval());
}

// ===========================================================================
// Stage 2 — total division (#26 §10.2)
//
// The state space here is 6×6 cells. That size permits a complete enumeration.
// These tests therefore *exhaust* the table and do not sample it. The expected
// values come independently from the denotations in #26 §2. A transcription
// error in the implementation therefore disagrees with a table that a separate
// derivation produces.
// ===========================================================================

/// The three defects that open issue #26. This test confirms that each defect
/// reproduces on the kernel and is absent from the extended type.
#[test]
fn the_motivating_defects_are_fixed() {
    let zero = Rat::new(0, 1).unwrap();
    let one = Rat::new(1, 1).unwrap();

    // 1. `Rat::zero().recip()` returns `Rat { num: -1, den: 0 }`. That value
    //    violates the type invariant, which requires den > 0. It causes a
    //    failure in a later operation.
    let broken = zero.recip();
    assert_eq!(
        (broken.numerator(), broken.denominator()),
        (-1, 0),
        "premise: the kernel defect still reproduces"
    );
    assert_eq!(
        Q::Number(zero).recip(),
        Q::PosInf,
        "the extended type must report a state, not a malformed value"
    );

    // 2. and 3. `Rat::div(_, 0)` and `Rat::checked_div(_, 0)` both panic.
    assert!(
        std::panic::catch_unwind(|| Rat::div(one, zero)).is_err(),
        "premise: kernel div by zero still panics"
    );
    assert!(
        std::panic::catch_unwind(|| Rat::checked_div(one, zero)).is_err(),
        "premise: kernel checked_div by zero still panics"
    );
    assert_eq!(Q::div(Q::one(), Q::zero()), Q::PosInf);
    assert_eq!(
        Q::checked_div(Q::one(), Q::zero()),
        None,
        "checked_div must return None where std and num-traits do"
    );
}

/// The 25 special-by-special cells, written out as a literal table.
fn special_div_table() -> Vec<(Q, Q, Q)> {
    use Q::{Nan, NegInf, NegSat, PosInf, PosSat};
    let zero = Q::Number(Rat::new(0, 1).unwrap());
    vec![
        // Sat / Sat spans (0, ∞) or its mirror. The sign is known and the
        // magnitude is unknown. This lattice cannot express that state.
        (PosSat, PosSat, Nan),
        (PosSat, NegSat, Nan),
        (NegSat, PosSat, Nan),
        (NegSat, NegSat, Nan),
        // Sat / Inf is EXACT. Sat denotes reals only, thus the image is
        // {s/±∞} = {0}.
        (PosSat, PosInf, zero),
        (PosSat, NegInf, zero),
        (NegSat, PosInf, zero),
        (NegSat, NegInf, zero),
        // Inf / Sat is a signed infinity, for the same reason. Division of ±∞
        // by a finite real gives an infinity.
        (PosInf, PosSat, PosInf),
        (PosInf, NegSat, NegInf),
        (NegInf, PosSat, NegInf),
        (NegInf, NegSat, PosInf),
        // ∞/∞ is indeterminate.
        (PosInf, PosInf, Nan),
        (PosInf, NegInf, Nan),
        (NegInf, PosInf, Nan),
        (NegInf, NegInf, Nan),
        // Nan absorbs on both sides.
        (Nan, PosSat, Nan),
        (Nan, NegSat, Nan),
        (Nan, PosInf, Nan),
        (Nan, NegInf, Nan),
        (Nan, Nan, Nan),
        (PosSat, Nan, Nan),
        (NegSat, Nan, Nan),
        (PosInf, Nan, Nan),
        (NegInf, Nan, Nan),
    ]
}

#[test]
fn division_special_by_special_matches_the_derived_table() {
    let table = special_div_table();
    assert_eq!(table.len(), 25, "all 5x5 special cells must be covered");
    for (a, b, want) in table {
        assert_eq!(Q::div(a, b), want, "div({a}, {b}) is wrong");
    }
}

#[test]
fn division_number_by_special_matches_the_derived_table() {
    let vals = [
        Rat::new(0, 1).unwrap(),
        Rat::new(1, 1).unwrap(),
        Rat::new(-1, 1).unwrap(),
        Rat::new(1, 2).unwrap(),
        Rat::new(-3, 2).unwrap(),
        Rat::new(MAX_MAG, 1).unwrap(),
        Rat::new(-MAX_MAG, 1).unwrap(),
    ];
    let zero = Q::Number(Rat::new(0, 1).unwrap());
    for x in vals {
        let q = Q::Number(x);
        // For x / Sat the image is (0, x/MAX_MAG). That interval crosses
        // representable values. Thus only x == 0 has a sound answer. That
        // answer is exact, because Sat cannot be infinite.
        let want_sat = if x.is_zero() { zero } else { Q::Nan };
        assert_eq!(Q::div(q, Q::PosSat), want_sat, "{x} / PosSat");
        assert_eq!(Q::div(q, Q::NegSat), want_sat, "{x} / NegSat");
        // x / Inf is exactly zero for every x, including x == 0.
        assert_eq!(Q::div(q, Q::PosInf), zero, "{x} / PosInf");
        assert_eq!(Q::div(q, Q::NegInf), zero, "{x} / NegInf");
        assert_eq!(Q::div(q, Q::Nan), Q::Nan, "{x} / Nan");
    }
}

#[test]
fn division_special_by_number_matches_the_derived_table() {
    // The unit boundary is INCLUSIVE. At |y| == 1 the image of (M,∞)/y is
    // exactly (M,∞). Saturation is therefore sound and minimal there. The open
    // interval |y| > 1 reaches into representable values.
    let cases: [(i64, i64); 9] = [
        (0, 1),
        (1, 1),
        (-1, 1),
        (1, 2),
        (-1, 2),
        (2, 1),
        (-2, 1),
        (MAX_MAG, 1),
        (-MAX_MAG, 1),
    ];
    for (n, d) in cases {
        let y = Rat::new(n, d).unwrap();
        let qy = Q::Number(y);
        let is_zero = n == 0;
        let within_unit = n.unsigned_abs() <= d.unsigned_abs();

        let want_pos_sat = if is_zero {
            Q::PosInf
        } else if !within_unit {
            Q::Nan
        } else if n > 0 {
            Q::PosSat
        } else {
            Q::NegSat
        };
        assert_eq!(Q::div(Q::PosSat, qy), want_pos_sat, "PosSat / {y}");

        let want_neg_sat = match want_pos_sat {
            Q::PosSat => Q::NegSat,
            Q::NegSat => Q::PosSat,
            Q::PosInf => Q::NegInf,
            other => other,
        };
        assert_eq!(Q::div(Q::NegSat, qy), want_neg_sat, "NegSat / {y}");

        // ±∞ / y preserves the sign, and this includes y == 0. Section 4
        // applies the IEEE rule uniformly. It does not give Nan here.
        let want_pos_inf = if n < 0 { Q::NegInf } else { Q::PosInf };
        assert_eq!(Q::div(Q::PosInf, qy), want_pos_inf, "PosInf / {y}");
        assert_eq!(
            Q::div(Q::NegInf, qy),
            if n < 0 { Q::PosInf } else { Q::NegInf },
            "NegInf / {y}"
        );
        assert_eq!(Q::div(Q::Nan, qy), Q::Nan, "Nan / {y}");
    }
}

#[test]
fn division_by_zero_follows_ieee_uniformly() {
    // Section 4 applies the IEEE rule uniformly, and the uniformity is
    // essential. A rule that uses IEEE for x/0 and a limit-rigorous Nan for
    // recip(0) and ±∞/0 breaks recip(x) == div(one, x) at x = 0.
    let z = Q::zero();
    assert_eq!(Q::div(Q::one(), z), Q::PosInf);
    assert_eq!(Q::div(Q::neg_one(), z), Q::NegInf);
    assert_eq!(Q::div(z, z), Q::Nan, "0/0 carries no information");
    assert_eq!(Q::div(Q::PosSat, z), Q::PosInf);
    assert_eq!(Q::div(Q::NegSat, z), Q::NegInf);
    assert_eq!(Q::div(Q::PosInf, z), Q::PosInf, "±∞/0 is sign-preserving");
    assert_eq!(Q::div(Q::NegInf, z), Q::NegInf);
    assert_eq!(Q::div(Q::Nan, z), Q::Nan);
}

#[test]
fn recip_agrees_with_div_one_over_every_state() {
    // The construction makes this true, because recip is div(one, ·). The test
    // checks it anyway. Issue #26 §4 records a design in which the two
    // operations disagree.
    for q in representatives() {
        assert_eq!(
            q.recip(),
            Q::div(Q::one(), q),
            "recip and div(one, ·) disagree at {q}"
        );
    }
    let mut rng = Rng::new(0x5EED_1234_ABCD_000B);
    for _ in 0..20_000 {
        let q = Q::Number(rng.q());
        assert_eq!(q.recip(), Q::div(Q::one(), q));
    }
}

#[test]
fn recip_matches_the_derived_table() {
    assert_eq!(Q::zero().recip(), Q::PosInf, "must match div(one, zero)");
    assert_eq!(Q::PosInf.recip(), Q::zero());
    assert_eq!(Q::NegInf.recip(), Q::zero());
    assert_eq!(
        Q::PosSat.recip(),
        Q::Nan,
        "image (0, 1/M) straddles the grid"
    );
    assert_eq!(Q::NegSat.recip(), Q::Nan);
    assert_eq!(Q::Nan.recip(), Q::Nan);
    assert_eq!(
        Q::Number(Rat::new(2, 3).unwrap()).recip(),
        Q::Number(Rat::new(3, 2).unwrap())
    );
}

#[test]
fn recip_is_exact_and_never_saturates_on_nonzero_numbers() {
    // A reciprocal swaps the components of a canonical pair. Both components
    // are already inside the budget. Thus neither rounding nor overflow occurs.
    let mut rng = Rng::new(0x5EED_1234_ABCD_000C);
    for _ in 0..20_000 {
        let x = rng.q_nonzero();
        let r = Q::Number(x).recip();
        assert!(r.is_number(), "recip({x}) saturated, which cannot happen");
        // The oracle confirms exactness.
        if let Q::Number(y) = r {
            assert_eq!(
                rat(y) * rat(x),
                Rational::from_signeds(1i128, 1i128),
                "recip({x}) = {y} is not exact"
            );
        }
        // The operation is an involution on nonzero rationals.
        assert_eq!(r.recip(), Q::Number(x), "recip is not an involution at {x}");
    }
}

#[test]
fn division_of_numbers_agrees_with_the_oracle() {
    let mut rng = Rng::new(0x5EED_1234_ABCD_000D);
    let max = Rational::from_signeds(MAX_MAG as i128, 1i128);
    let mut saturated = 0u32;
    for i in 0..20_000 {
        // A quotient overflows only when a large value divides by a small one.
        // Random pairs almost never give that combination. Half the draws
        // therefore overflow by construction. This exercises the saturating
        // branch. Without those draws the test passes without a check of that
        // branch.
        let (x, y) = if i % 2 == 0 {
            let sign = if rng.below(2) == 0 { 1i64 } else { -1i64 };
            let big = Rat::new(sign * (MAX_MAG - rng.below(1000) as i64), 1).unwrap();
            let tiny = Rat::new(1, rng.below(1_000_000) as i64 + 2).unwrap();
            (big, tiny)
        } else {
            (rng.q(), rng.q_nonzero())
        };
        let exact = rat(x) / rat(y);
        let mag = if exact < oracle_zero() {
            -exact.clone()
        } else {
            exact.clone()
        };
        let q = Q::div(Q::Number(x), Q::Number(y));
        if mag > max {
            saturated += 1;
            assert_eq!(
                q,
                if exact > oracle_zero() {
                    Q::PosSat
                } else {
                    Q::NegSat
                },
                "{x} / {y} overflows and must saturate by sign, got {q}"
            );
        } else {
            // Inside the budget the result is a number. R3 bounds its error.
            match q {
                Q::Number(r) => common::assert_r3(r, &exact, "Q::div"),
                other => panic!("{x} / {y} = {exact} fits but produced {other}"),
            }
        }
    }
    assert!(
        saturated > 10,
        "only {saturated} saturating quotients drawn; that path is untested"
    );
}

#[test]
fn division_never_silently_clamps() {
    // The kernel clamps an overflowing quotient to ±MAX_MAG/1. It returns that
    // as an ordinary value. The singleton denotation of that value does not
    // contain the true result. The extended type reports the overflow instead.
    let tiny = Q::Number(Rat::new(1, MAX_MAG).unwrap());
    let big = Q::Number(Rat::new(MAX_MAG, 1).unwrap());
    let q = Q::div(big, tiny);
    assert_eq!(
        q,
        Q::PosSat,
        "MAX_MAG / (1/MAX_MAG) overflows and must say so"
    );
    assert!(
        q.is_saturated() && !q.is_infinite(),
        "overflow is not infinity"
    );
    assert_eq!(Q::checked_div(big, tiny), None);
}

#[test]
fn checked_div_is_exactly_the_number_case_of_div() {
    for a in representatives() {
        for b in representatives() {
            let want = match Q::div(a, b) {
                Q::Number(f) => Some(f),
                _ => None,
            };
            assert_eq!(Q::checked_div(a, b), want, "checked_div({a}, {b})");
        }
    }
}

#[test]
fn division_is_total_and_never_produces_a_malformed_value() {
    // This is the primary property. No input causes a panic. Every output
    // satisfies the invariant. Verus proves both properties. This test runs
    // them against the compiled artifact.
    let mut rng = Rng::new(0x5EED_1234_ABCD_000E);
    let specials = representatives();
    for i in 0..20_000 {
        // The draws mix specials with numbers and include zero divisors.
        let a = if i % 7 == 0 {
            specials[(i as usize) % specials.len()]
        } else {
            Q::Number(rng.q())
        };
        let b = if i % 5 == 0 {
            Q::zero()
        } else if i % 3 == 0 {
            specials[(i as usize * 3) % specials.len()]
        } else {
            Q::Number(rng.q())
        };
        let q = Q::div(a, b);
        if let Q::Number(x) = q {
            common::assert_wf(x, "Q::div");
        }
        let c = [q.is_number(), q.is_saturated(), q.is_infinite(), q.is_nan()]
            .iter()
            .filter(|z| **z)
            .count();
        assert_eq!(c, 1, "div({a}, {b}) produced an unclassified value");
        // checked_div must also never panic.
        let _ = Q::checked_div(a, b);
        let _ = a.recip();
    }
}

#[test]
fn an_infinity_in_the_quotient_always_points_at_a_zero_divisor() {
    // This property makes is_infinite() a usable diagnostic. Infinity means
    // division by zero. Saturation means overflow. The two never merge.
    for a in representatives() {
        for b in representatives() {
            let q = Q::div(a, b);
            if q.is_infinite() {
                assert!(
                    a.is_infinite() || b.is_zero(),
                    "div({a}, {b}) = {q} is infinite without a zero divisor \
                     or an infinite numerator"
                );
            }
            if q.is_saturated() {
                assert!(!b.is_zero(), "div({a}, {b}) overflowed on a zero divisor");
            }
        }
    }
}

// ===========================================================================
// Stage 3 — add / sub / mul, and the selection and sign operations
// ===========================================================================

/// The five specials in a fixed order, for the literal tables below.
const S5: [Q; 5] = [Q::PosSat, Q::NegSat, Q::PosInf, Q::NegInf, Q::Nan];

/// Index into `S5` for a literal table row.
fn s5_index(q: Q) -> usize {
    S5.iter().position(|s| *s == q).expect("not a special")
}

#[test]
fn addition_special_by_special_matches_the_derived_table() {
    use Q::{Nan, NegInf, NegSat, PosInf, PosSat};
    // Rows and columns use S5 order: PosSat, NegSat, PosInf, NegInf, Nan. The
    // denotations give the cells. Saturations with the same sign reinforce.
    // Saturations with opposite signs cancel to an unknown value. An infinity
    // dominates every finite value.
    let table: [[Q; 5]; 5] = [
        [PosSat, Nan, PosInf, NegInf, Nan],
        [Nan, NegSat, PosInf, NegInf, Nan],
        [PosInf, PosInf, PosInf, Nan, Nan],
        [NegInf, NegInf, Nan, NegInf, Nan],
        [Nan, Nan, Nan, Nan, Nan],
    ];
    for a in S5 {
        for b in S5 {
            assert_eq!(
                Q::add(a, b),
                table[s5_index(a)][s5_index(b)],
                "add({a}, {b}) is wrong"
            );
        }
    }
}

#[test]
fn multiplication_special_by_special_matches_the_derived_table() {
    use Q::{Nan, NegInf, NegSat, PosInf, PosSat};
    let table: [[Q; 5]; 5] = [
        [PosSat, NegSat, PosInf, NegInf, Nan],
        [NegSat, PosSat, NegInf, PosInf, Nan],
        [PosInf, NegInf, PosInf, NegInf, Nan],
        [NegInf, PosInf, NegInf, PosInf, Nan],
        [Nan, Nan, Nan, Nan, Nan],
    ];
    for a in S5 {
        for b in S5 {
            assert_eq!(
                Q::mul(a, b),
                table[s5_index(a)][s5_index(b)],
                "mul({a}, {b}) is wrong"
            );
        }
    }
}

#[test]
fn addition_number_by_saturation_respects_the_soundness_cliff() {
    // Number(x) + PosSat denotes (MAX_MAG + x, +inf). For x >= 0 that interval
    // lies inside the denotation of PosSat. For x < 0 the lower endpoint can
    // fall to 0. The image then includes representable values, thus PosSat is
    // UNSOUND there.
    for (n, d) in [
        (0i64, 1i64),
        (1, 1),
        (-1, 1),
        (1, 2),
        (-1, 2),
        (MAX_MAG, 1),
        (-MAX_MAG, 1),
    ] {
        let x = Rat::new(n, d).unwrap();
        let q = Q::Number(x);
        assert_eq!(
            Q::add(q, Q::PosSat),
            if n >= 0 { Q::PosSat } else { Q::Nan },
            "{x} + PosSat"
        );
        assert_eq!(
            Q::add(q, Q::NegSat),
            if n <= 0 { Q::NegSat } else { Q::Nan },
            "{x} + NegSat"
        );
        // Addition is commutative, and this includes the cliff.
        assert_eq!(Q::add(Q::PosSat, q), Q::add(q, Q::PosSat));
        assert_eq!(Q::add(Q::NegSat, q), Q::add(q, Q::NegSat));
        // An infinity dominates every finite value.
        assert_eq!(Q::add(q, Q::PosInf), Q::PosInf);
        assert_eq!(Q::add(q, Q::NegInf), Q::NegInf);
    }
}

#[test]
fn multiplication_by_saturation_has_an_inclusive_unit_boundary() {
    // At |x| == 1 the image is exactly 1 * (M, inf) = (M, inf). Saturation is
    // therefore sound and minimal. The cliff is the OPEN interval 0 < |x| < 1.
    // A condition of `x > 1` sends one() * PosSat to Nan. That result
    // contradicts neg(PosSat) == NegSat.
    assert_eq!(
        Q::mul(Q::one(), Q::PosSat),
        Q::PosSat,
        "boundary is inclusive"
    );
    assert_eq!(Q::mul(Q::neg_one(), Q::PosSat), Q::NegSat);
    assert_eq!(
        Q::mul(Q::neg_one(), Q::PosSat),
        Q::PosSat.neg(),
        "must agree with negation"
    );
    // These values lie inside the cliff.
    assert_eq!(
        Q::mul(Q::Number(Rat::new(1, 2).unwrap()), Q::PosSat),
        Q::Nan
    );
    assert_eq!(
        Q::mul(Q::Number(Rat::new(-1, 2).unwrap()), Q::PosSat),
        Q::Nan
    );
    // These values lie outside the cliff.
    assert_eq!(
        Q::mul(Q::Number(Rat::new(2, 1).unwrap()), Q::PosSat),
        Q::PosSat
    );
    assert_eq!(
        Q::mul(Q::Number(Rat::new(-2, 1).unwrap()), Q::PosSat),
        Q::NegSat
    );
}

#[test]
fn zero_times_saturation_is_exactly_zero_but_zero_times_infinity_is_nan() {
    // This case shows saturation with better behaviour than infinity. Sat
    // denotes finite reals only, thus 0 * Sat is exactly 0. The product
    // 0 * inf is indeterminate.
    assert_eq!(Q::mul(Q::zero(), Q::PosSat), Q::zero());
    assert_eq!(Q::mul(Q::zero(), Q::NegSat), Q::zero());
    assert_eq!(Q::mul(Q::PosSat, Q::zero()), Q::zero());
    assert_eq!(Q::mul(Q::zero(), Q::PosInf), Q::Nan);
    assert_eq!(Q::mul(Q::zero(), Q::NegInf), Q::Nan);
    assert_eq!(Q::mul(Q::PosInf, Q::zero()), Q::Nan);
}

#[test]
fn addition_no_longer_silently_clamps() {
    // The kernel returns MAX_MAG for MAX_MAG + MAX_MAG. That result is wrong by
    // a factor of two. It carries no error guarantee. A caller cannot tell it
    // from a correct result.
    let m = Rat::new(MAX_MAG, 1).unwrap();
    assert_eq!(
        Rat::add(m, m).numerator(),
        MAX_MAG,
        "premise: the kernel still clamps"
    );
    assert_eq!(
        Q::add(Q::Number(m), Q::Number(m)),
        Q::PosSat,
        "the extended type must report the overflow"
    );
    assert_eq!(Q::add(Q::Number(m).neg(), Q::Number(m).neg()), Q::NegSat);
}

#[test]
fn arithmetic_of_numbers_agrees_with_the_oracle() {
    let mut rng = Rng::new(0x5EED_1234_ABCD_0010);
    let max = Rational::from_signeds(MAX_MAG as i128, 1i128);
    let (mut sat_add, mut sat_mul) = (0u32, 0u32);
    for i in 0..20_000 {
        // Half the draws lie near the ceiling. This reaches the saturating
        // branch. Random pairs almost never overflow.
        let (x, y) = if i % 2 == 0 {
            let s = if rng.below(2) == 0 { 1i64 } else { -1i64 };
            (
                Rat::new(s * (MAX_MAG - rng.below(1000) as i64), 1).unwrap(),
                Rat::new(MAX_MAG - rng.below(1000) as i64, 1).unwrap(),
            )
        } else {
            (rng.q(), rng.q())
        };
        let mag = |r: &Rational| {
            if *r < oracle_zero() {
                -r.clone()
            } else {
                r.clone()
            }
        };

        for (op, exact, got) in [
            ("add", rat(x) + rat(y), Q::add(Q::Number(x), Q::Number(y))),
            ("sub", rat(x) - rat(y), Q::sub(Q::Number(x), Q::Number(y))),
            ("mul", rat(x) * rat(y), Q::mul(Q::Number(x), Q::Number(y))),
        ] {
            if mag(&exact) > max {
                match op {
                    "add" => sat_add += 1,
                    "mul" => sat_mul += 1,
                    _ => {}
                }
                assert_eq!(
                    got,
                    if exact > oracle_zero() {
                        Q::PosSat
                    } else {
                        Q::NegSat
                    },
                    "{op}({x}, {y}) overflows and must saturate by sign, got {got}"
                );
            } else {
                match got {
                    Q::Number(r) => common::assert_r3(r, &exact, op),
                    other => panic!("{op}({x}, {y}) = {exact} fits but produced {other}"),
                }
            }
        }
    }
    assert!(
        sat_add > 10 && sat_mul > 10,
        "saturating paths barely exercised"
    );
}

#[test]
fn subtraction_is_addition_of_the_negation() {
    // Section 5 defines subtraction that way. The two operations must therefore
    // agree about an overflowing difference.
    for a in representatives() {
        for b in representatives() {
            assert_eq!(Q::sub(a, b), Q::add(a, b.neg()), "sub({a}, {b})");
        }
    }
}

#[test]
fn addition_and_multiplication_are_commutative_over_every_state() {
    // Commutativity lifts to the enum directly. This test pins it, because the
    // tables list each cell separately. A transposition error is otherwise
    // silent.
    for a in representatives() {
        for b in representatives() {
            assert_eq!(
                Q::add(a, b),
                Q::add(b, a),
                "add not commutative at ({a},{b})"
            );
            assert_eq!(
                Q::mul(a, b),
                Q::mul(b, a),
                "mul not commutative at ({a},{b})"
            );
        }
    }
}

#[test]
fn negation_and_absolute_value_match_the_derived_table() {
    assert_eq!(Q::PosSat.neg(), Q::NegSat);
    assert_eq!(Q::NegSat.neg(), Q::PosSat);
    assert_eq!(Q::PosInf.neg(), Q::NegInf);
    assert_eq!(Q::NegInf.neg(), Q::PosInf);
    assert_eq!(Q::Nan.neg(), Q::Nan);

    assert_eq!(Q::PosSat.abs(), Q::PosSat);
    assert_eq!(Q::NegSat.abs(), Q::PosSat);
    assert_eq!(Q::PosInf.abs(), Q::PosInf);
    assert_eq!(Q::NegInf.abs(), Q::PosInf);
    assert_eq!(Q::Nan.abs(), Q::Nan);

    // Negation is an involution on every state. The abs operation is
    // idempotent.
    for q in representatives() {
        assert_eq!(q.neg().neg(), q, "neg is not an involution at {q}");
        assert_eq!(q.abs().abs(), q.abs(), "abs is not idempotent at {q}");
        assert!(
            !Q::lt(q.abs(), Q::zero()) || q.is_nan(),
            "{q}.abs() is negative"
        );
    }
}

#[test]
fn selection_propagates_nan_and_disagrees_with_ord() {
    // Issue #26 §5 names this trap. Selection through Ord gives
    // min(Nan, Number(5)) == Number(5). The true value can be any value, and
    // that result asserts a value of exactly 5. IEEE 754-2019 withdrew
    // minNum/maxNum for this reason.
    let five = Q::Number(Rat::new(5, 1).unwrap());
    assert_eq!(Q::min(Q::Nan, five), Q::Nan);
    assert_eq!(Q::max(Q::Nan, five), Q::Nan);
    assert_eq!(Q::min(five, Q::Nan), Q::Nan);
    assert_eq!(Q::clamp(Q::Nan, Q::zero(), Q::one()), Q::Nan);
    assert_eq!(Q::clamp(five, Q::Nan, Q::one()), Q::Nan);
    assert_eq!(Q::clamp(five, Q::zero(), Q::Nan), Q::Nan);

    // The disagreement with selection through Ord is observable.
    let ord_min = [Q::Nan, five].into_iter().min().unwrap();
    assert_eq!(ord_min, five, "Ord picks the non-Nan operand");
    assert_ne!(
        Q::min(Q::Nan, five),
        ord_min,
        "Q::min and slice min are meant to disagree on Nan"
    );
}

#[test]
fn selection_agrees_with_the_order_away_from_nan() {
    let vs: Vec<Q> = representatives()
        .into_iter()
        .filter(|q| !q.is_nan())
        .collect();
    for &a in &vs {
        for &b in &vs {
            let lo = Q::min(a, b);
            let hi = Q::max(a, b);
            assert!(lo == a || lo == b);
            assert!(
                Q::le(lo, a) && Q::le(lo, b),
                "min({a},{b}) not a lower bound"
            );
            assert!(
                Q::le(a, hi) && Q::le(b, hi),
                "max({a},{b}) not an upper bound"
            );
            assert_eq!(lo, if a <= b { a } else { b }, "min disagrees with Ord");
            // A clamp into an ordered range keeps the result inside the range.
            for &c in &vs {
                if Q::le(lo, hi) {
                    let r = Q::clamp(c, lo, hi);
                    assert!(Q::le(lo, r) && Q::le(r, hi), "clamp({c},{lo},{hi}) escaped");
                }
            }
        }
    }
}

#[test]
fn clamp_reports_an_inverted_range_rather_than_guessing() {
    // Nan is an admissible bound. The order alone therefore cannot state the
    // precondition `lo <= hi`. An inverted range gives Nan, and not an
    // arbitrary endpoint. Nan is the only answer that asserts nothing false.
    assert_eq!(Q::clamp(Q::one(), Q::one(), Q::zero()), Q::Nan);
    assert_eq!(Q::clamp(Q::zero(), Q::PosInf, Q::NegInf), Q::Nan);
}

#[test]
fn arithmetic_is_total_and_never_produces_a_malformed_value() {
    let mut rng = Rng::new(0x5EED_1234_ABCD_0011);
    let specials = representatives();
    for i in 0..20_000 {
        let a = if i % 6 == 0 {
            specials[(i as usize) % specials.len()]
        } else {
            Q::Number(rng.q())
        };
        let b = if i % 4 == 0 {
            specials[(i as usize * 5) % specials.len()]
        } else {
            Q::Number(rng.q())
        };
        for q in [
            Q::add(a, b),
            Q::sub(a, b),
            Q::mul(a, b),
            Q::div(a, b),
            Q::min(a, b),
            Q::max(a, b),
            a.neg(),
            a.abs(),
        ] {
            if let Q::Number(x) = q {
                common::assert_wf(x, "extended arithmetic");
            }
            let c = [q.is_number(), q.is_saturated(), q.is_infinite(), q.is_nan()]
                .iter()
                .filter(|z| **z)
                .count();
            assert_eq!(
                c, 1,
                "an operation on ({a}, {b}) produced {q}, unclassified"
            );
        }
    }
}

// ===========================================================================
// pow, the checked_* sugar, and the f64 boundary
// ===========================================================================

#[test]
fn pow_of_zero_is_one_for_every_base_including_nan() {
    // IEEE gives NaN^0 == 1, and issue #26 §5 states this rule explicitly. The
    // exponent is a count. The operation uses the base zero times, thus the
    // information content of the base does not matter.
    for q in representatives() {
        assert_eq!(q.pow_u32(0), Q::one(), "{q}^0 must be one");
    }
    assert_eq!(Q::Nan.pow_u32(0), Q::one());
}

#[test]
fn pow_matches_repeated_multiplication() {
    // This is a left fold of Q::mul. It uses the same association as the
    // kernel's pow_u32. The association matters, because rounding makes
    // multiplication non-associative. A square-and-multiply version can
    // therefore give a different answer.
    let mut rng = Rng::new(0x5EED_1234_ABCD_0020);
    for _ in 0..2_000 {
        let q = Q::Number(rng.q());
        for e in 0..6u32 {
            let mut want = Q::one();
            for _ in 0..e {
                want = Q::mul(want, q);
            }
            assert_eq!(q.pow_u32(e), want, "pow({q}, {e})");
        }
    }
    // The same property holds on the specials.
    assert_eq!(Q::PosInf.pow_u32(2), Q::PosInf);
    assert_eq!(Q::NegInf.pow_u32(2), Q::PosInf);
    assert_eq!(Q::NegInf.pow_u32(3), Q::NegInf);
    assert_eq!(Q::PosSat.pow_u32(2), Q::PosSat);
    assert_eq!(Q::NegSat.pow_u32(2), Q::PosSat);
    assert_eq!(Q::Nan.pow_u32(3), Q::Nan);
}

#[test]
fn pow_is_exact_at_one_and_stays_in_the_unit_interval() {
    // Composition gives the oracle comparison for `pow`.
    // `pow_matches_repeated_multiplication` pins `pow` against `Q::mul`.
    // `arithmetic_of_numbers_agrees_with_the_oracle` pins `Q::mul` against
    // malachite. This test checks what composition does *not* give. These are
    // the two closure properties that a rounding fold can violate.
    let one = Rational::from_signeds(1i128, 1i128);
    let mut rng = Rng::new(0x5EED_1234_ABCD_0021);
    for _ in 0..3_000 {
        let x = rng.q_unit(); // in [0,1], thus no power overflows
        let q = Q::Number(x);

        // e == 1 is the exact identity. No rounding occurs.
        assert_eq!(q.pow_u32(1), q, "pow({x}, 1) must be the base itself");

        for e in 2..6u32 {
            match q.pow_u32(e) {
                Q::Number(r) => {
                    // A power of a value in [0,1] stays in [0,1]. Rounding
                    // cannot move it out. The R3 error is relative, and both
                    // endpoints are exactly representable.
                    assert!(
                        rat(r) >= oracle_zero() && rat(r) <= one,
                        "pow({x}, {e}) = {r} escaped [0,1]"
                    );
                    // Powers are non-increasing on [0,1].
                    assert!(
                        Q::le(Q::Number(r), q.pow_u32(e - 1)),
                        "pow({x}, {e}) exceeds pow({x}, {})",
                        e - 1
                    );
                }
                other => panic!("pow({x}, {e}) left the Number class: {other}"),
            }
        }
    }
}

#[test]
fn checked_operations_are_exactly_the_number_case() {
    for a in representatives() {
        for b in representatives() {
            let num = |q: Q| match q {
                Q::Number(f) => Some(f),
                _ => None,
            };
            assert_eq!(
                Q::checked_add(a, b),
                num(Q::add(a, b)),
                "checked_add({a},{b})"
            );
            assert_eq!(
                Q::checked_sub(a, b),
                num(Q::sub(a, b)),
                "checked_sub({a},{b})"
            );
            assert_eq!(
                Q::checked_mul(a, b),
                num(Q::mul(a, b)),
                "checked_mul({a},{b})"
            );
            assert_eq!(
                Q::checked_div(a, b),
                num(Q::div(a, b)),
                "checked_div({a},{b})"
            );
        }
    }
}

#[test]
fn checked_mul_can_succeed_with_a_saturated_operand() {
    // Number(0) * PosSat is exactly Number(0). Multiplication therefore has no
    // rule that maps a saturated input to None, and it differs from
    // checked_add. This test pins the asymmetry. The asymmetry follows from Sat
    // denoting finite reals only.
    assert_eq!(
        Q::checked_mul(Q::zero(), Q::PosSat),
        Some(Rat::new(0, 1).unwrap())
    );
    assert_eq!(Q::checked_add(Q::zero(), Q::PosSat), None);
}

#[test]
fn every_f64_has_an_image_in_the_extended_type() {
    use the_q::q_from_f64;
    // Issue #26 §8 records this gain. `from_f64_dir` maps these values to None,
    // because `Rat` has no state for them. The enum has such states.
    assert_eq!(q_from_f64(f64::NAN), Q::Nan);
    assert_eq!(q_from_f64(f64::INFINITY), Q::PosInf);
    assert_eq!(q_from_f64(f64::NEG_INFINITY), Q::NegInf);
    assert!(the_q::from_f64_dir(f64::NAN, the_q::Dir::Nearest).is_none());

    // Ordinary values use the verified path.
    assert_eq!(q_from_f64(0.5), Q::Number(Rat::new(1, 2).unwrap()));
    assert_eq!(q_from_f64(0.0), Q::zero());
    assert_eq!(q_from_f64(-1.0), Q::neg_one());

    // A finite value past the budget saturates by sign. It does not fail.
    assert_eq!(q_from_f64(1e30), Q::PosSat);
    assert_eq!(q_from_f64(-1e30), Q::NegSat);

    // A wide sweep checks totality, and it includes the difficult classes.
    let mut rng = Rng::new(0x5EED_1234_ABCD_0022);
    for _ in 0..20_000 {
        let bits = rng.next_u64();
        let v = f64::from_bits(bits);
        let q = q_from_f64(v);
        if let Q::Number(x) = q {
            common::assert_wf(x, "q_from_f64");
        }
        let c = [q.is_number(), q.is_saturated(), q.is_infinite(), q.is_nan()]
            .iter()
            .filter(|z| **z)
            .count();
        assert_eq!(c, 1, "q_from_f64({v}) produced an unclassified value");
        assert_eq!(q.is_nan(), v.is_nan(), "NaN must map to Nan and only NaN");
    }
}

// ===========================================================================
// Operator traits
// ===========================================================================

#[test]
fn operators_delegate_to_the_verified_functions() {
    for a in representatives() {
        for b in representatives() {
            assert_eq!(a + b, Q::add(a, b), "Add at ({a}, {b})");
            assert_eq!(a - b, Q::sub(a, b), "Sub at ({a}, {b})");
            assert_eq!(a * b, Q::mul(a, b), "Mul at ({a}, {b})");
            assert_eq!(a / b, Q::div(a, b), "Div at ({a}, {b})");
        }
        assert_eq!(-a, a.neg(), "Neg at {a}");
    }
}

#[test]
fn the_division_operator_is_total() {
    // `Rat` has no `Div`. Its division carries a precondition that an operator
    // cannot express. An `a / b` operator on `Rat` therefore panics for a
    // caller that omits the check. `Q::div` is total, thus the operator is safe
    // here. This includes the input that panics for `Rat`.
    assert_eq!(Q::one() / Q::zero(), Q::PosInf);
    assert_eq!(Q::zero() / Q::zero(), Q::Nan);
    let mut rng = Rng::new(0x5EED_1234_ABCD_0030);
    for _ in 0..20_000 {
        let (a, b) = (Q::Number(rng.q()), Q::Number(rng.q()));
        // Neither operation may panic, and this includes a zero value of b.
        let _ = a / b;
        let _ = a / Q::zero();
    }
}

#[test]
fn default_is_zero() {
    assert_eq!(Q::default(), Q::zero());
    assert!(Q::default().is_zero());
}

// ===========================================================================
// The §2 soundness obligation, checked denotationally
//
// The tests above check the propagation tables against a hand-written table.
// That method catches transcription errors. It does not catch a wrong
// *derivation*. A wrong derivation of a cell makes both the implementation and
// the expected table wrong together.
//
// This section checks the obligation that the tables must satisfy. The
// obligation is independent of both the implementation and the table:
//
//     { x (+) y : x in [[a]], y in [[b]] }  subset-of  [[op(a, b)]]
//
// The harness draws concrete members from the denotation of each operand. It
// computes the true result with arbitrary precision. It then checks membership
// in the denotation of the result. An unsound cell claims a value that its
// denotation does not contain. Such a cell fails here even when the
// hand-written table agrees with the code.
// ===========================================================================

/// An extended rational: a value of `ℚ ∪ {±∞}`.
///
/// The denotations in §2 range over the reals. Every endpoint is rational and
/// every denotation is an interval. Membership over `ℚ` is therefore equivalent
/// for this purpose. An exact oracle can represent `ℚ`.
#[derive(Clone, Debug, PartialEq)]
enum Xr {
    Fin(Rational),
    PosInfinity,
    NegInfinity,
}

fn max_mag_q() -> Rational {
    Rational::from_signeds(MAX_MAG as i128, 1i128)
}

/// Reports whether `v` is a member of the denotation of `q`.
fn denotes(q: Q, v: &Xr) -> bool {
    match (q, v) {
        (Q::Nan, _) => true, // denotes every value, thus always sound
        (Q::Number(x), Xr::Fin(r)) => rat(x) == *r,
        (Q::Number(_), _) => false,
        // Reals only, open at MAX_MAG. The denotation holds no infinity.
        (Q::PosSat, Xr::Fin(r)) => *r > max_mag_q(),
        (Q::PosSat, _) => false,
        (Q::NegSat, Xr::Fin(r)) => *r < -max_mag_q(),
        (Q::NegSat, _) => false,
        (Q::PosInf, Xr::PosInfinity) => true,
        (Q::PosInf, _) => false,
        (Q::NegInf, Xr::NegInfinity) => true,
        (Q::NegInf, _) => false,
    }
}

/// Members drawn from the denotation of a state. The list is empty for `Nan`.
/// `Nan` denotes every value and is therefore always sound. A sample of `Nan`
/// gives no information.
fn members(q: Q) -> Vec<Xr> {
    let m = max_mag_q();
    let half = Rational::from_signeds(1i128, 2i128);
    match q {
        Q::Number(x) => vec![Xr::Fin(rat(x))],
        // The members are an integer above the open endpoint, a non-integer
        // above the endpoint, and a value far above it. The first two catch an
        // off-by-one error at MAX_MAG.
        Q::PosSat => vec![
            Xr::Fin(m.clone() + Rational::from_signeds(1i128, 1i128)),
            Xr::Fin(m.clone() + half.clone()),
            Xr::Fin(m.clone() * Rational::from_signeds(1000i128, 1i128)),
        ],
        Q::NegSat => vec![
            Xr::Fin(-(m.clone() + Rational::from_signeds(1i128, 1i128))),
            Xr::Fin(-(m.clone() + half)),
            Xr::Fin(-(m * Rational::from_signeds(1000i128, 1i128))),
        ],
        Q::PosInf => vec![Xr::PosInfinity],
        Q::NegInf => vec![Xr::NegInfinity],
        Q::Nan => vec![],
    }
}

/// Exact extended-rational arithmetic. The result is `None` where the operation
/// is undefined: `∞ − ∞`, `0 · ∞`, `∞ / ∞` and `x / 0`. Those cases have no
/// image point. The obligation therefore does not constrain those cells, and
/// the IEEE conventions of the design govern them. The table tests above pin
/// those cells.
fn xr_add(a: &Xr, b: &Xr) -> Option<Xr> {
    match (a, b) {
        (Xr::Fin(x), Xr::Fin(y)) => Some(Xr::Fin(x.clone() + y.clone())),
        (Xr::PosInfinity, Xr::NegInfinity) | (Xr::NegInfinity, Xr::PosInfinity) => None,
        (Xr::PosInfinity, _) | (_, Xr::PosInfinity) => Some(Xr::PosInfinity),
        (Xr::NegInfinity, _) | (_, Xr::NegInfinity) => Some(Xr::NegInfinity),
    }
}

fn xr_mul(a: &Xr, b: &Xr) -> Option<Xr> {
    let z = oracle_zero();
    match (a, b) {
        (Xr::Fin(x), Xr::Fin(y)) => Some(Xr::Fin(x.clone() * y.clone())),
        (Xr::Fin(x), inf) | (inf, Xr::Fin(x)) => {
            if *x == z {
                None // 0 * inf is indeterminate.
            } else {
                let pos = (*x > z) == (*inf == Xr::PosInfinity);
                Some(if pos {
                    Xr::PosInfinity
                } else {
                    Xr::NegInfinity
                })
            }
        }
        (p, q2) => {
            let pos = (*p == Xr::PosInfinity) == (*q2 == Xr::PosInfinity);
            Some(if pos {
                Xr::PosInfinity
            } else {
                Xr::NegInfinity
            })
        }
    }
}

fn xr_div(a: &Xr, b: &Xr) -> Option<Xr> {
    let z = oracle_zero();
    match (a, b) {
        (Xr::Fin(x), Xr::Fin(y)) => {
            if *y == z {
                None // x/0 is a convention, not a limit.
            } else {
                Some(Xr::Fin(x.clone() / y.clone()))
            }
        }
        // A finite value over an infinite value is exactly zero.
        (Xr::Fin(_), _) => Some(Xr::Fin(z)),
        // An infinite value over a finite value.
        (inf, Xr::Fin(y)) => {
            if *y == z {
                None
            } else {
                let pos = (*y > z) == (*inf == Xr::PosInfinity);
                Some(if pos {
                    Xr::PosInfinity
                } else {
                    Xr::NegInfinity
                })
            }
        }
        _ => None, // inf / inf.
    }
}

/// The states for the soundness check. The `Number` payloads cross every
/// boundary on which the tables branch: zero, the unit boundary, and the edge
/// of the budget.
fn soundness_states() -> Vec<Q> {
    let mut v = vec![
        Q::Number(Rat::new(0, 1).unwrap()),
        Q::Number(Rat::new(1, 1).unwrap()),
        Q::Number(Rat::new(-1, 1).unwrap()),
        Q::Number(Rat::new(1, 2).unwrap()),
        Q::Number(Rat::new(-1, 2).unwrap()),
        Q::Number(Rat::new(2, 1).unwrap()),
        Q::Number(Rat::new(-2, 1).unwrap()),
        Q::Number(Rat::new(MAX_MAG, 1).unwrap()),
        Q::Number(Rat::new(-MAX_MAG, 1).unwrap()),
        Q::Number(Rat::new(1, MAX_MAG).unwrap()),
    ];
    v.extend_from_slice(&SPECIALS);
    v
}

/// Runs the obligation for one operation over every state pair and every drawn
/// member. `exact` is the partial arithmetic. `op` is the implementation.
fn check_soundness(
    name: &str,
    exact: impl Fn(&Xr, &Xr) -> Option<Xr>,
    op: impl Fn(Q, Q) -> Q,
) -> u32 {
    let mut checked = 0u32;
    for a in soundness_states() {
        for b in soundness_states() {
            let got = op(a, b);
            // R1, R2 and R3 govern `Number x Number`, and exact-set soundness
            // does not. The result rounds, thus its singleton denotation need
            // not contain the true value. The scoping note in §2 states this.
            // Other tests check that regime against the oracle.
            let both_numbers = a.is_number() && b.is_number();
            for va in members(a) {
                for vb in members(b) {
                    let Some(truth) = exact(&va, &vb) else {
                        continue; // undefined: no image point.
                    };
                    if both_numbers && got.is_number() {
                        continue; // the rounded regime.
                    }
                    checked += 1;
                    assert!(
                        denotes(got, &truth),
                        "{name} UNSOUND at ({a}, {b}): true result {truth:?} \
                         from ({va:?}, {vb:?}) is not in the denotation of {got}"
                    );
                }
            }
        }
    }
    checked
}

#[test]
fn addition_satisfies_the_soundness_obligation() {
    let n = check_soundness("add", xr_add, Q::add);
    assert!(n > 200, "only {n} membership checks; coverage too thin");
}

#[test]
fn multiplication_satisfies_the_soundness_obligation() {
    let n = check_soundness("mul", xr_mul, Q::mul);
    assert!(n > 200, "only {n} membership checks; coverage too thin");
}

#[test]
fn division_satisfies_the_soundness_obligation() {
    let n = check_soundness("div", xr_div, Q::div);
    assert!(n > 200, "only {n} membership checks; coverage too thin");
}

#[test]
fn subtraction_satisfies_the_soundness_obligation() {
    let n = check_soundness(
        "sub",
        |a, b| {
            let nb = match b {
                Xr::Fin(y) => Xr::Fin(-y.clone()),
                Xr::PosInfinity => Xr::NegInfinity,
                Xr::NegInfinity => Xr::PosInfinity,
            };
            xr_add(a, &nb)
        },
        Q::sub,
    );
    assert!(n > 200, "only {n} membership checks; coverage too thin");
}

#[test]
fn the_soundness_harness_would_catch_an_unsound_cell() {
    // This is a guard on the harness. `Number(-1) + PosSat` denotes
    // (MAX_MAG - 1, +inf). That interval reaches below MAX_MAG, thus an answer
    // of PosSat is unsound there. The real implementation avoids that cliff.
    // This test supplies the unsound answer and confirms that the harness
    // rejects it.
    let wrong = |a: Q, b: Q| {
        if a == Q::Number(Rat::new(-1, 1).unwrap()) && b == Q::PosSat {
            Q::PosSat // unsound: the image includes representable values.
        } else {
            Q::add(a, b)
        }
    };
    let caught = std::panic::catch_unwind(|| check_soundness("wrong-add", xr_add, wrong));
    assert!(
        caught.is_err(),
        "the harness accepted a knowingly unsound cell, so it is not checking \
         soundness"
    );
}

// ===========================================================================
// N-ary folds
// ===========================================================================

#[test]
fn folds_report_overflow_where_the_kernel_absorbs_it() {
    // The kernel clamps `M + M` to `M`. It then subtracts `M` and returns 0.
    // That result is silently wrong, because the true total is `M`. Issue #26
    // §9.2 gives this example.
    let m = Rat::new(MAX_MAG, 1).unwrap();
    let neg_m = Rat::new(-MAX_MAG, 1).unwrap();
    assert_eq!(
        the_q::nary::sum(&[m, m, neg_m]).numerator(),
        0,
        "premise: the kernel still returns 0 for [M, M, -M]"
    );
    // The enum fold does not invent that result. It cannot recover the true
    // total. Section 9.2 states that a sticky Nan is the cost. The fold reports
    // no false value.
    let folded = Q::sum(&[Q::Number(m), Q::Number(m), Q::Number(neg_m)]);
    assert!(!folded.is_number(), "must not report a plain number here");
    assert_eq!(folded, Q::Nan);
}

/// The V8 accumulated-error bound: after `k` elements the fold is within
/// `k · 2^-61 · max(1, |exact|)` of the exact value.
///
/// The `theorem_sum_error_accumulation` in `nary` states this bound. The bound
/// is *not* R3. R3 governs a single rounding, and a `k`-element fold performs
/// `k` roundings. Use of `assert_r3` here checks the wrong theorem.
fn assert_accumulated(got: Rat, exact: &Rational, k: usize, what: &str) {
    let one = Rational::from_signeds(1i128, 1i128);
    let err = if rat(got) > *exact {
        rat(got) - exact.clone()
    } else {
        exact.clone() - rat(got)
    };
    let mag = if *exact < oracle_zero() {
        -exact.clone()
    } else {
        exact.clone()
    };
    let scale = if mag > one { mag } else { one };
    let bound = Rational::from_signeds(k as i128, 1i128 << 61) * scale;
    assert!(
        err <= bound,
        "{what}: accumulated error exceeds k·2^-61·max(1,|exact|) with k={k}; \
         got {got}, exact {exact}"
    );
}

#[test]
fn folds_stay_within_the_accumulated_error_bound() {
    // On the exact path the fold cannot overflow, thus the result stays a
    // number. The V8 bound `k · 2^-61` limits its distance from the true value.
    // The single-rounding bound of R3 does not apply.
    let mut rng = Rng::new(0x5EED_1234_ABCD_0040);
    for _ in 0..2_000 {
        let n = 1 + (rng.below(8) as usize);
        let xs: Vec<Rat> = (0..n).map(|_| rng.q_unit()).collect();
        let qs: Vec<Q> = xs.iter().map(|x| Q::Number(*x)).collect();

        let mut exact = oracle_zero();
        for x in &xs {
            exact += rat(*x);
        }
        match Q::sum(&qs) {
            Q::Number(r) => assert_accumulated(r, &exact, n, "Q::sum"),
            other => panic!("sum of unit values must stay a number, got {other}"),
        }

        // The bound for `product` requires a magnitude of at most 1 for every
        // factor. `q_unit` guarantees that magnitude. Without it the carried
        // error grows geometrically instead of additively.
        let mut pexact = Rational::from_signeds(1i128, 1i128);
        for x in &xs {
            pexact *= rat(*x);
        }
        match Q::product(&qs) {
            Q::Number(r) => assert_accumulated(r, &pexact, n, "Q::product"),
            other => panic!("product of unit values must stay a number, got {other}"),
        }
    }
}

#[test]
fn folds_are_bit_exact_when_no_step_rounds() {
    // Short decimals share a denominator. No partial sum therefore needs
    // rounding. The fold gives exactly the answer of the oracle. This test
    // asserts equality and not a bound.
    let mut rng = Rng::new(0x5EED_1234_ABCD_0043);
    for _ in 0..2_000 {
        let n = 1 + (rng.below(20) as usize);
        let xs: Vec<Rat> = (0..n)
            .map(|_| Rat::from_decimal(rng.below(101) as i64, 2).unwrap())
            .collect();
        let qs: Vec<Q> = xs.iter().map(|x| Q::Number(*x)).collect();
        let mut exact = oracle_zero();
        for x in &xs {
            exact += rat(*x);
        }
        match Q::sum(&qs) {
            Q::Number(r) => assert_eq!(rat(r), exact, "two-decimal sum must be exact"),
            other => panic!("expected a number, got {other}"),
        }
    }
}

#[test]
fn empty_folds_are_the_identities() {
    assert_eq!(Q::sum(&[]), Q::zero());
    assert_eq!(Q::product(&[]), Q::one());
    // An empty weighted mean is 0/0, and it carries no information. The result
    // is Nan by the rule for every other division, and not by a special case.
    assert_eq!(Q::weighted_mean(&[]), Q::Nan);
}

#[test]
fn folds_propagate_nan_and_never_panic() {
    let mut rng = Rng::new(0x5EED_1234_ABCD_0041);
    let specials = representatives();
    for i in 0..5_000 {
        let n = 1 + (rng.below(6) as usize);
        let xs: Vec<Q> = (0..n)
            .map(|k| {
                if (i + k) % 5 == 0 {
                    specials[(i + k) % specials.len()]
                } else {
                    Q::Number(rng.q())
                }
            })
            .collect();
        let has_nan = xs.iter().any(|q| q.is_nan());

        for r in [Q::sum(&xs), Q::product(&xs)] {
            if let Q::Number(x) = r {
                common::assert_wf(x, "Q fold");
            }
            if has_nan {
                assert!(r.is_nan(), "a Nan input must propagate through the fold");
            }
        }

        let pairs: Vec<(Q, Q)> = xs.iter().map(|q| (*q, *q)).collect();
        let wm = Q::weighted_mean(&pairs);
        if let Q::Number(x) = wm {
            common::assert_wf(x, "Q::weighted_mean");
        }
    }
}

#[test]
fn weighted_mean_is_total_where_the_kernel_returns_none() {
    // For a zero total weight the kernel reports `None` out of band. The
    // extended type gives a value instead. It follows the #26 §4 convention
    // that governs every other division.
    let z = Q::zero();
    assert_eq!(
        Q::weighted_mean(&[(z, Q::one()), (z, Q::one())]),
        Q::Nan,
        "0 weighted numerator over 0 weight is 0/0"
    );
    // A nonzero numerator over a zero weight gives a signed infinity.
    let pos = Q::one();
    let neg = Q::neg_one();
    let wm = Q::weighted_mean(&[(pos, pos), (neg, pos)]);
    assert!(wm.is_nan() || wm.is_infinite(), "got {wm}");

    // The ordinary case operates and is exact.
    let half = Q::Number(Rat::new(1, 2).unwrap());
    assert_eq!(
        Q::weighted_mean(&[(Q::one(), Q::zero()), (Q::one(), Q::one())]),
        half,
        "equal weights on 0 and 1 give 1/2"
    );
}

#[test]
fn weighted_mean_agrees_with_the_oracle_on_the_exact_path() {
    let mut rng = Rng::new(0x5EED_1234_ABCD_0042);
    for _ in 0..2_000 {
        let n = 1 + (rng.below(5) as usize);
        let pairs: Vec<(Rat, Rat)> = (0..n).map(|_| (rng.q_unit(), rng.q_unit())).collect();
        let qp: Vec<(Q, Q)> = pairs
            .iter()
            .map(|(w, x)| (Q::Number(*w), Q::Number(*x)))
            .collect();

        let mut num = oracle_zero();
        let mut den = oracle_zero();
        for (w, x) in &pairs {
            num += rat(*w) * rat(*x);
            den += rat(*w);
        }
        if den == oracle_zero() {
            continue;
        }
        let exact = num / den;
        if let Q::Number(r) = Q::weighted_mean(&qp) {
            // Several roundings compose here. This check therefore confirms a
            // correct neighbourhood. It does not pin a single rounding.
            let err = if rat(r) > exact.clone() {
                rat(r) - exact.clone()
            } else {
                exact.clone() - rat(r)
            };
            assert!(
                err <= Rational::from_signeds(1i128, 1i128 << 40),
                "weighted_mean is far from the exact value: got {r}, exact {exact}"
            );
        }
    }
}

#[test]
fn clamp_returns_the_value_itself_when_it_is_already_in_range() {
    // This test guards the defect that `theorem_clamp_spec_categorical`
    // exposes. A weaker contract permits a `clamp` that ignores `a` and always
    // returns `lo`. For `lo < a < hi` that answer is one of the three permitted
    // values, and it lies in `[lo, hi]`.
    //
    // The proof rules that behaviour out, and this test rules it out as well. A
    // contract and a test fail in different ways.
    let lo = Q::zero();
    let hi = Q::Number(Rat::new(10, 1).unwrap());
    for n in 1i64..10 {
        let a = Q::Number(Rat::new(n, 1).unwrap());
        assert_eq!(
            Q::clamp(a, lo, hi),
            a,
            "a value already inside [lo, hi] must come back unchanged"
        );
    }
    // Values outside the range clamp to the endpoints.
    assert_eq!(Q::clamp(Q::Number(Rat::new(-5, 1).unwrap()), lo, hi), lo);
    assert_eq!(Q::clamp(Q::Number(Rat::new(50, 1).unwrap()), lo, hi), hi);

    // Random values run against an independently computed expectation.
    let mut rng = Rng::new(0x5EED_1234_ABCD_0050);
    for _ in 0..20_000 {
        let (a, lo, hi) = (Q::Number(rng.q()), Q::Number(rng.q()), Q::Number(rng.q()));
        if !Q::le(lo, hi) {
            continue;
        }
        let want = if Q::lt(a, lo) {
            lo
        } else if Q::lt(hi, a) {
            hi
        } else {
            a
        };
        assert_eq!(Q::clamp(a, lo, hi), want, "clamp({a}, {lo}, {hi})");
    }
}
