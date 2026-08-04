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
