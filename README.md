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

## Honesty notice

With rounding, `add`/`mul` are commutative (always proven) but **not
associative in general**. Associativity holds on the exact path. The
consuming engine's order-independence claims therefore hold exactly for
small cases and up to the accumulated error bound in general.

## Verification status

The crate is structured for Verus verification. Proof obligations (V1-V8)
are documented in source comments. The current implementation compiles with
standard `cargo build`; Verus annotation is pending toolchain setup.

See `TRUSTED.md` for the single `external_body` function (`to_f64`).

## Testing

```sh
cargo test              # unit + integration tests
cargo test --features serde  # include serde round-trip tests
```

The oracle test suite (`tests/oracle.rs`) uses `malachite-q` as a
**dev-dependency only** (LGPL-3.0, never in the release binary).
