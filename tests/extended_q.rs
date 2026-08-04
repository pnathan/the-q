//! The extended `Q`: classification, predicates, ordering, and the boundaries.
//!
//! # What is proven, and what these tests add
//!
//! The predicates in `ext.rs` are specified against the *ghost model* — `is_one`
//! is `x.n() == x.d()`, a statement about the denoted rational — and implemented
//! by delegating to the kernel's own verified predicates. Those two are
//! genuinely different statements, so the postconditions have real content:
//! replacing the body with the classic wrong `is_one` (numerator is 1, ignoring
//! the denominator) **fails verification**, checked by doing it.
//!
//! That is worth stating precisely, because the dangerous shape is nearby. Had
//! the specification been written to mirror the body — `is_one` specified as
//! "the numerator field is 1" and implemented as exactly that — it would verify
//! happily with the same mistake duplicated into both, and would establish
//! nothing at all. The protection here comes from specifying against `n()`/`d()`
//! rather than against the fields, and from delegating rather than
//! reimplementing.
//!
//! The differential suite against `malachite-q` is still the load-bearing check,
//! for a reason verification cannot cover: it tests the *compiled artifact*,
//! with an arbitrary-precision oracle that shares no code and no authorship with
//! anything here. A proof that has not been run against the artifact is a
//! hypothesis about the artifact. `predicates_would_catch_a_mutation` guards the
//! guard, confirming the generator actually draws inputs that separate a right
//! implementation from a wrong one.
//!
//! The order's laws (totality, antisymmetry, transitivity) are genuine theorems
//! proven in `ext.rs`, and are re-checked here exhaustively over the
//! representation classes for the same artifact-level reason.

mod common;

use common::{rat, zero as oracle_zero, Rng};
use malachite_q::Rational;
use std::collections::BTreeMap;
use std::str::FromStr;
use the_q::{ParseQError, Rat, Sign, MAX_MAG, Q};

/// The five payload-free states.
const SPECIALS: [Q; 5] = [Q::PosSat, Q::NegSat, Q::PosInf, Q::NegInf, Q::Nan];

/// A spread of representation classes covering every variant, with several
/// numbers so the `Number`-vs-`Number` case is exercised inside the sweeps.
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

    // The distinction that earns saturation its place in the type: an overflow
    // is not a division by zero, and `is_saturated` is how a caller tells them
    // apart. If these ever collapse, the diagnostic value is gone.
    assert!(!Q::PosSat.is_infinite(), "saturation is not infinity");
    assert!(!Q::PosInf.is_saturated(), "infinity is not saturation");
}

#[test]
fn there_is_deliberately_no_is_finite() {
    // Not a behavioural test — a design guard. `PosSat` denotes reals above the
    // budget, which are finite, so any `is_finite()` would have to either lie
    // about `PosSat` or mean the same as `is_number()`. Issue #26 §1 rules it
    // out. This test exists so that adding one is a deliberate act that breaks
    // a named test rather than a quiet addition.
    //
    // `PosSat` is finite in the mathematical sense but is not a number in this
    // type's sense; that is exactly the distinction the predicate set encodes.
    assert!(!Q::PosSat.is_number());
    assert!(!Q::PosSat.is_infinite());
}

// ===========================================================================
// C2 — the value predicates, against an independent oracle
// ===========================================================================

/// The oracle's answers for a `Rat`, computed with arbitrary precision and no
/// reference to anything in `the-q`.
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
    // `q()` above rarely lands in [0,1]; `q_unit()` lands there always, so this
    // is the case `in_unit_interval` actually has to get right.
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
    // Issue #26 §5 states these rather than leaving them emergent, so they are
    // pinned here. On the saturations these are not conventions but the true
    // answers — (MAX_MAG, +inf) contains neither 0 nor 1 nor any of [0,1].
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
    // The sign is the one piece of information the specials do carry, and
    // discarding it was the explicitly rejected alternative in #26 §4.
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
    // A guard on the differential itself. The suite above is only meaningful if
    // it would fail when the implementation is wrong, so here is the wrong
    // implementation, checked to disagree with the real one on the very inputs
    // the differential draws.
    //
    // The mutation is the classic one for this shape: `is_one` written as
    // "numerator is 1" without also requiring the denominator to be 1.
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
    // The deliberate IEEE departure. Under IEEE every ordered comparison with
    // NaN is false, which is precisely what forbids a total order; `f64`
    // sidesteps it by having no `Ord` at all and quarantining the total order
    // in `total_cmp`. This type takes the other trade.
    for q in representatives() {
        assert!(Q::le(q, q), "{q} is not <= itself");
        assert_eq!(q, q, "{q} is not == itself");
        assert!(!Q::lt(q, q), "{q} is < itself");
    }
    assert_eq!(Q::Nan, Q::Nan, "Nan == Nan must hold to keep Eq lawful");
}

#[test]
fn order_agrees_with_equality_and_hashing() {
    // `Hash` must be consistent with `Eq`, which is what lets `Q` be a key.
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
    // The soundness fact behind the placement: every NegSat value is below
    // every Number, and every PosSat value above, so the order on
    // representations agrees with the order on denoted values here.
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
    // The point of the spelling: a reader (or a downstream parser) must not be
    // able to mistake a saturated result for an exact value.
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
    // Following `f64::from_str`, since IEEE 754 is this design's reference model.
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
    // Following `i64::from_str`. A parser that silently trims is a parser that
    // silently accepts `"1 / 2"` in a data file.
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
    // `Q::new(1, 0)` is `PosInf` because a *computation* divided by zero and the
    // result must be some value. `"1/0"` in an input stream is a malformed
    // numeral instead, and accepting it would hide the typo that produced it.
    // Display never emits a zero denominator, so this costs no round-trip.
    for text in ["0/0", "1/0", "-1/0"] {
        assert_eq!(
            Q::from_str(text),
            Err(ParseQError::ZeroDenominator),
            "{text:?} must be rejected, not mapped to a special"
        );
    }
    // ... and the contrast with the total constructor is real, not accidental.
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
    // `i64::MAX + 1` is a well-formed numeral that does not fit; `abc` is not a
    // numeral at all. Collapsing the two loses the information a caller needs to
    // tell "your data is too big" from "your data is corrupt".
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
    // One spelling shared by both, per #26 §8 — not two that can drift apart.
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
    // The extension must not have changed how a bare `Rat` encodes; consumers
    // of `Rat` are not part of this break.
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
    // Thirteen shapes a hostile or buggy producer can emit. Each must be an
    // error rather than a silently wrong value.
    let bad = [
        r#"[1,0]"#,                   // zero denominator
        r#"[1]"#,                     // too short
        r#"[1,2,3]"#,                 // too long
        r#"[]"#,                      // empty
        r#""sat""#,                   // a plausible but wrong spelling
        r#""-sat""#,                  // the other plausible wrong spelling
        r#""NAN""#,                   // wrong case: machine-written, so strict
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
    // `[1,-2]` is *accepted*, because `Rat::new` normalises the sign onto the
    // numerator and `-1/2` is perfectly representable. Pinned explicitly rather
    // than left to the rejection list, because "un-normalised input" looks like
    // it ought to be an error and is not — the canonicalisation is the whole
    // reason it need not be.
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
    // The documented caveat, made executable. `deserialize_any` is what limits
    // the untagged encoding to formats that can report the next value's kind;
    // JSON can, so this succeeds — the test exists to name the dependency, so
    // that swapping in a non-self-describing codec fails somewhere that
    // explains why.
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
    // The defect this design exists to remove: `Rat::new(_, 0)` has to report
    // failure out of band, and `Rat::zero().recip()` produced a value violating
    // the type invariant. Here every input maps to a value in the type.
    assert_eq!(Q::new(1, 0), Q::PosInf);
    assert_eq!(Q::new(-1, 0), Q::NegInf);
    assert_eq!(Q::new(0, 0), Q::Nan);
    assert_eq!(Q::new(1, 2), Q::Number(Rat::new(1, 2).unwrap()));

    // Above the budget but finite: saturates by sign rather than failing.
    assert_eq!(Q::new(i64::MAX, 1), Q::PosSat);
    assert_eq!(Q::new(i64::MIN, 1), Q::NegSat);
    assert_eq!(Q::new(i64::MAX, -1), Q::NegSat);
}

#[test]
fn new_does_not_saturate_a_tiny_value_with_an_oversized_denominator() {
    // A regression test for a real bug. `Rat::new` returns `None` for two
    // different reasons — the value is too big, or the reduced *denominator* is
    // too big while the value is tiny — and an implementation that saturates on
    // "Rat::new said None" conflates them.
    //
    // `1 / i64::MIN` is about -1.08e-19. Calling that `NegSat` would assert
    // |value| > MAX_MAG of a value in (-1, 0): an unsound denotation, and
    // precisely the silent-wrong-answer class this type exists to remove.
    // It must round instead, which under R3 lands on zero.
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
    // The boundary is the *value*, and MAX_MAG itself is representable, so the
    // cut is strictly above it. This is what `magnitude_fits` encodes.
    assert_eq!(Q::new(MAX_MAG, 1), Q::Number(Rat::new(MAX_MAG, 1).unwrap()));
    assert_eq!(
        Q::new(-MAX_MAG, 1),
        Q::Number(Rat::new(-MAX_MAG, 1).unwrap())
    );
    assert_eq!(Q::new(MAX_MAG + 1, 1), Q::PosSat);
    assert_eq!(Q::new(-MAX_MAG - 1, 1), Q::NegSat);

    // Two large components whose *ratio* is small: never saturation.
    assert_eq!(
        Q::new(i64::MAX, i64::MAX),
        Q::Number(Rat::new(1, 1).unwrap())
    );
    assert!(!Q::new(i64::MAX - 1, i64::MAX).is_saturated());
    assert!(!Q::new(i64::MIN, i64::MAX).is_saturated());
}

#[test]
fn new_agrees_with_rat_new_wherever_rat_new_succeeds() {
    // Rounding a value that is already representable returns it unchanged (R1),
    // so the total constructor must be a conservative extension of the partial
    // one — never a different answer, only an answer where there was none.
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
    // The independent check: saturation must mean |value| > MAX_MAG according to
    // arbitrary-precision arithmetic, not according to this crate's own
    // reduction code.
    let mut rng = Rng::new(0x5EED_1234_ABCD_000A);
    let max = Rational::from_signeds(MAX_MAG as i128, 1i128);
    let mut saturating = 0u32;
    for i in 0..20_000 {
        // Uniform i64 pairs almost never saturate: |n/d| > 2^62 needs a large
        // numerator over a *small* denominator, and a random 64-bit denominator
        // is overwhelmingly large. Half the draws therefore use a small
        // denominator, so the saturating regime is actually reached. (Without
        // this the test passes vacuously — which is how this was caught.)
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
        // Whatever it is, it is classified exactly once.
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
// The state space here is 6×6 cells, which is small enough to enumerate
// completely. These tests therefore *exhaust* the table rather than sampling
// it, and the expected values are written out independently from the
// denotations in #26 §2 — so a transcription slip in the implementation
// disagrees with a table derived separately, instead of being copied into both.
// ===========================================================================

/// The three defects that open issue #26, each confirmed to reproduce on the
/// kernel and to be gone from the extended type.
#[test]
fn the_motivating_defects_are_fixed() {
    let zero = Rat::new(0, 1).unwrap();
    let one = Rat::new(1, 1).unwrap();

    // 1. `Rat::zero().recip()` returns `Rat { num: -1, den: 0 }` — a value that
    //    violates the type invariant (den must be > 0) and detonates later.
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
        // Sat / Sat spans (0, ∞) or its mirror: sign known, magnitude entirely
        // unknown, which is the one thing this lattice cannot express.
        (PosSat, PosSat, Nan),
        (PosSat, NegSat, Nan),
        (NegSat, PosSat, Nan),
        (NegSat, NegSat, Nan),
        // Sat / Inf is EXACT: Sat denotes reals only, so the image is {s/±∞} = {0}.
        (PosSat, PosInf, zero),
        (PosSat, NegInf, zero),
        (NegSat, PosInf, zero),
        (NegSat, NegInf, zero),
        // Inf / Sat is a signed infinity, for the same reason — dividing ±∞ by a
        // finite real leaves it infinite.
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
        // x / Sat: the image is (0, x/MAX_MAG), which straddles representable
        // values — so only x == 0 has a sound answer, and there it is exact
        // precisely because Sat cannot be infinite.
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
    // The unit boundary is INCLUSIVE: at |y| == 1 the image of (M,∞)/y is
    // exactly (M,∞), so saturation is sound and minimal there. It is the open
    // interval |y| > 1 that dips into representable territory.
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

        // ±∞ / y is sign-preserving, including at y == 0 — §4 applies the IEEE
        // rule uniformly rather than making this case Nan.
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
    // §4's decision, and the uniformity is the point: an earlier draft used the
    // IEEE rule for x/0 but a limit-rigorous Nan for recip(0) and ±∞/0, which
    // broke recip(x) == div(one, x) at exactly x = 0.
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
    // True by construction — recip IS div(one, ·) — and checked anyway, because
    // #26 §4 records these coming apart in an earlier draft of the design.
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
    // Reciprocating swaps a canonical pair whose components were both already
    // inside the budget, so neither rounding nor overflow is reachable.
    let mut rng = Rng::new(0x5EED_1234_ABCD_000C);
    for _ in 0..20_000 {
        let x = rng.q_nonzero();
        let r = Q::Number(x).recip();
        assert!(r.is_number(), "recip({x}) saturated, which cannot happen");
        // Exactness, against the oracle.
        if let Q::Number(y) = r {
            assert_eq!(
                rat(y) * rat(x),
                Rational::from_signeds(1i128, 1i128),
                "recip({x}) = {y} is not exact"
            );
        }
        // An involution on nonzero rationals.
        assert_eq!(r.recip(), Q::Number(x), "recip is not an involution at {x}");
    }
}

#[test]
fn division_of_numbers_agrees_with_the_oracle() {
    let mut rng = Rng::new(0x5EED_1234_ABCD_000D);
    let max = Rational::from_signeds(MAX_MAG as i128, 1i128);
    let mut saturated = 0u32;
    for i in 0..20_000 {
        // A quotient only overflows when a large value is divided by a tiny
        // one, which random pairs essentially never produce. Half the draws are
        // therefore built to overflow, so the saturating branch is actually
        // exercised — without this the test passes without testing it, which is
        // how the omission was caught.
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
            // Inside the budget the result is a number, and R3 bounds its error.
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
    // The kernel clamps an overflowing quotient to ±MAX_MAG/1 and returns it as
    // an ordinary value — a singleton denotation that does not contain the true
    // result. The extended type must report the overflow instead.
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
    // The headline property: no input panics, and every output satisfies the
    // invariant. Verus proves both; this runs them against the artifact.
    let mut rng = Rng::new(0x5EED_1234_ABCD_000E);
    let specials = representatives();
    for i in 0..20_000 {
        // Mix specials with numbers, and deliberately include zero divisors.
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
        // checked_div must never panic either.
        let _ = Q::checked_div(a, b);
        let _ = a.recip();
    }
}

#[test]
fn an_infinity_in_the_quotient_always_points_at_a_zero_divisor() {
    // What makes is_infinite() a usable diagnostic: infinity means division by
    // zero, saturation means overflow, and the two never blur.
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
    // Rows and columns in S5 order: PosSat, NegSat, PosInf, NegInf, Nan.
    // Derived from the denotations: same-signed saturations reinforce,
    // opposite-signed ones cancel to something entirely unknown, and an
    // infinity dominates anything finite.
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
    // Number(x) + PosSat denotes (MAX_MAG + x, +inf). For x >= 0 that sits
    // inside PosSat's denotation. For x < 0 the lower endpoint can fall to 0,
    // so the image includes representable values and PosSat would be UNSOUND.
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
        // Addition is commutative, including across the cliff.
        assert_eq!(Q::add(Q::PosSat, q), Q::add(q, Q::PosSat));
        assert_eq!(Q::add(Q::NegSat, q), Q::add(q, Q::NegSat));
        // An infinity dominates any finite value.
        assert_eq!(Q::add(q, Q::PosInf), Q::PosInf);
        assert_eq!(Q::add(q, Q::NegInf), Q::NegInf);
    }
}

#[test]
fn multiplication_by_saturation_has_an_inclusive_unit_boundary() {
    // At |x| == 1 the image is exactly 1 * (M, inf) = (M, inf), so saturation
    // is sound and minimal. The cliff is the OPEN interval 0 < |x| < 1.
    // An earlier draft of §5 wrote this as `x > 1`, which sent one() * PosSat
    // to Nan and contradicted neg(PosSat) == NegSat.
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
    // Just inside the cliff.
    assert_eq!(
        Q::mul(Q::Number(Rat::new(1, 2).unwrap()), Q::PosSat),
        Q::Nan
    );
    assert_eq!(
        Q::mul(Q::Number(Rat::new(-1, 2).unwrap()), Q::PosSat),
        Q::Nan
    );
    // Just outside it.
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
    // The single clearest case of saturation being better behaved than
    // infinity: Sat denotes finite reals only, so 0 * Sat is exactly 0, while
    // 0 * inf is genuinely indeterminate.
    assert_eq!(Q::mul(Q::zero(), Q::PosSat), Q::zero());
    assert_eq!(Q::mul(Q::zero(), Q::NegSat), Q::zero());
    assert_eq!(Q::mul(Q::PosSat, Q::zero()), Q::zero());
    assert_eq!(Q::mul(Q::zero(), Q::PosInf), Q::Nan);
    assert_eq!(Q::mul(Q::zero(), Q::NegInf), Q::Nan);
    assert_eq!(Q::mul(Q::PosInf, Q::zero()), Q::Nan);
}

#[test]
fn addition_no_longer_silently_clamps() {
    // The kernel returns MAX_MAG for MAX_MAG + MAX_MAG: wrong by a factor of
    // two, carrying no error guarantee, indistinguishable from a real result.
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
        // Half the draws are built near the ceiling so the saturating branch is
        // actually reached; random pairs almost never overflow.
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
    // §5 defines it that way, so the two must never disagree about an
    // overflowing difference.
    for a in representatives() {
        for b in representatives() {
            assert_eq!(Q::sub(a, b), Q::add(a, b.neg()), "sub({a}, {b})");
        }
    }
}

#[test]
fn addition_and_multiplication_are_commutative_over_every_state() {
    // Commutativity lifts to the enum trivially, and is worth pinning because
    // the tables are written out cell by cell and a transposition slip would
    // otherwise be silent.
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

    // Negation is an involution on every state; abs is idempotent.
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
    // The trap #26 §5 names explicitly. Ord-based selection would give
    // min(Nan, Number(5)) == Number(5): the true value could be anything and
    // the result asserts it is exactly 5. IEEE withdrew minNum/maxNum in
    // 754-2019 for precisely this reason.
    let five = Q::Number(Rat::new(5, 1).unwrap());
    assert_eq!(Q::min(Q::Nan, five), Q::Nan);
    assert_eq!(Q::max(Q::Nan, five), Q::Nan);
    assert_eq!(Q::min(five, Q::Nan), Q::Nan);
    assert_eq!(Q::clamp(Q::Nan, Q::zero(), Q::one()), Q::Nan);
    assert_eq!(Q::clamp(five, Q::Nan, Q::one()), Q::Nan);
    assert_eq!(Q::clamp(five, Q::zero(), Q::Nan), Q::Nan);

    // ...and the disagreement with Ord-based selection is real, not theoretical.
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
            // clamp into an ordered range keeps the result inside it.
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
    // With Nan admissible as a bound, `lo <= hi` cannot be a precondition
    // stated on the order alone; an inverted range yields Nan rather than an
    // arbitrary endpoint, which is the only answer that asserts nothing false.
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
    // IEEE's NaN^0 == 1, which #26 §5 states rather than leaving emergent: the
    // exponent is a count, so the base's informativeness is irrelevant when the
    // base is used zero times.
    for q in representatives() {
        assert_eq!(q.pow_u32(0), Q::one(), "{q}^0 must be one");
    }
    assert_eq!(Q::Nan.pow_u32(0), Q::one());
}

#[test]
fn pow_matches_repeated_multiplication() {
    // A left fold of Q::mul, the same association as the kernel's pow_u32 —
    // which matters, because with rounding multiplication is not associative,
    // so a square-and-multiply version could give a different answer.
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
    // And on the specials.
    assert_eq!(Q::PosInf.pow_u32(2), Q::PosInf);
    assert_eq!(Q::NegInf.pow_u32(2), Q::PosInf);
    assert_eq!(Q::NegInf.pow_u32(3), Q::NegInf);
    assert_eq!(Q::PosSat.pow_u32(2), Q::PosSat);
    assert_eq!(Q::NegSat.pow_u32(2), Q::PosSat);
    assert_eq!(Q::Nan.pow_u32(3), Q::Nan);
}

#[test]
fn pow_is_exact_at_one_and_stays_in_the_unit_interval() {
    // The oracle comparison for `pow` comes for free by composition:
    // `pow_matches_repeated_multiplication` pins it against `Q::mul`, and
    // `arithmetic_of_numbers_agrees_with_the_oracle` pins `Q::mul` against
    // malachite. What is checked here is what composition does *not* give — the
    // two closure properties a rounding fold could plausibly violate.
    let one = Rational::from_signeds(1i128, 1i128);
    let mut rng = Rng::new(0x5EED_1234_ABCD_0021);
    for _ in 0..3_000 {
        let x = rng.q_unit(); // in [0,1], so no power can overflow
        let q = Q::Number(x);

        // e == 1 is the identity, exactly — no rounding may creep in.
        assert_eq!(q.pow_u32(1), q, "pow({x}, 1) must be the base itself");

        for e in 2..6u32 {
            match q.pow_u32(e) {
                Q::Number(r) => {
                    // A power of a value in [0,1] stays in [0,1], and rounding
                    // cannot push it out: R3's error is relative, and both
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
    // Number(0) * PosSat is exactly Number(0), so unlike checked_add there is
    // no "a saturated input means None" rule. Pinned because the asymmetry is
    // surprising and follows directly from Sat denoting finite reals only.
    assert_eq!(
        Q::checked_mul(Q::zero(), Q::PosSat),
        Some(Rat::new(0, 1).unwrap())
    );
    assert_eq!(Q::checked_add(Q::zero(), Q::PosSat), None);
}

#[test]
fn every_f64_has_an_image_in_the_extended_type() {
    use the_q::q_from_f64;
    // The win #26 §8 calls unclaimed: from_f64_dir maps these to None because
    // Rat has nowhere to put them, and the enum does.
    assert_eq!(q_from_f64(f64::NAN), Q::Nan);
    assert_eq!(q_from_f64(f64::INFINITY), Q::PosInf);
    assert_eq!(q_from_f64(f64::NEG_INFINITY), Q::NegInf);
    assert!(the_q::from_f64_dir(f64::NAN, the_q::Dir::Nearest).is_none());

    // Ordinary values still go through the verified path.
    assert_eq!(q_from_f64(0.5), Q::Number(Rat::new(1, 2).unwrap()));
    assert_eq!(q_from_f64(0.0), Q::zero());
    assert_eq!(q_from_f64(-1.0), Q::neg_one());

    // Finite but past the budget: saturates by sign rather than failing.
    assert_eq!(q_from_f64(1e30), Q::PosSat);
    assert_eq!(q_from_f64(-1e30), Q::NegSat);

    // Totality over a wide sweep, including the awkward classes.
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
