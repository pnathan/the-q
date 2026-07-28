# the-q

Exact-with-verified-rounding rational arithmetic for subjective-logic fusion.

## The Q type

`Q` is a bounded rational number `num/den` with `i64` components, designed
to serve as the numeric backbone of a Josang-style belief fusion engine.

**Invariants** (every value, at all times):
- **I1 (canonical):** `den > 0`, `gcd(|num|, den) == 1`, `num == 0 => den == 1`
- **I2 (bounded):** `|num| <= 2^62 - 1`, `den <= 2^62 - 1`

Canonical form gives structural equality = mathematical equality. `Eq`,
`Ord`, and `Hash` are all sound. `Copy` — it's a plain 128-bit value type,
no heap, trivially `Send + Sync`.

## Arithmetic model

All intermediate computation is done exactly in `i128`. The 2^62 budget
guarantees every intermediate fits (worst case: add numerator < 2^125,
well within `i128`). After the exact computation:

1. GCD-reduce the result
2. If both components fit the budget -> **return exact** (R1)
3. Otherwise -> **dyadic-snap round** with `|error| <= 2^{-60} * max(1, |exact|)` (R3)

Consequence: any computation whose exact values all fit the budget is
**end-to-end exact**. Small investigations pay zero rounding.

## Interval arithmetic

`Interval` wraps a pair of `Q` values `[lo, hi]` with correct outward
rounding. All operations (add, sub, mul, div) use directed rounding to
guarantee the result interval contains the true value for every point
in the input intervals.

Lipschitz error propagation is built in: given a function's Lipschitz
constant, `lipschitz_widen` and `lipschitz_tighten` bound the output
without evaluating every point.

## Honesty notice

With rounding, `add`/`mul` are commutative (always proven) but **not
associative in general**. Associativity holds on the exact path. The
consuming engine's order-independence claims therefore hold exactly for
small cases and up to the accumulated error bound in general.

## Verification status

**Machine-checked (Verus, 17 proofs, 0 errors):**
- GCD on u64: full proof of correctness (divisibility spec, loop invariant, termination)
- Ghost model: `q_eq`, `q_le`, `q_lt`, `q_inv`, `int_abs` spec functions
- Spec-level lemmas: commutativity (add, mul), identity elements (zero, one),
  negation involution, negation/abs preserve invariant, multiplication by zero

**Tested (125 tests):**
- 64 unit tests (Q arithmetic, interval ops, rounding, constructors)
- 18 malachite-q oracle differential tests (exact-path + R3 bounds +
  10k-op fold chains + cross-thread determinism)
- 43 proptest property tests (invariant preservation, commutativity,
  associativity, distributivity, directed rounding contracts, R3 bounds,
  determinism, constructor rejection, serde round-trip)

See `TRUSTED.md` for the single `external_body` function (`to_f64`).

## Testing

```sh
cargo test                      # all 125 tests
cargo test --features serde     # include serde round-trip
cargo test --test proptest_tests  # property-based tests only
cargo test --test oracle        # malachite-q differential tests only
```

The oracle test suite (`tests/oracle.rs`) uses `malachite-q` as a
**dev-dependency only** (LGPL-3.0, never in the release binary).

## Verification

Requires Verus v0.2026.07.18+ and Rust toolchain 1.96.0:

```sh
verus src/lib.rs --crate-type=lib
```
