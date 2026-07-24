# the-q

Bounded, canonical rational arithmetic (`Q`) with a verified-rounding
design, built as the numeric backbone for a rational-closed rewrite of a
subjective-logic fusion engine. Full spec: this README summarizes it; the
authoritative version is the design document this crate was built from
(see "Design provenance" below).

## Status: partially Verus-verified

**Read this before relying on this crate for anything safety-critical.**
[Verus](https://github.com/verus-lang/verus) **is wired into CI**
(`.github/workflows/ci.yml`, `verus` job) and is machine-checking real
proofs, not just documented contracts. Per-obligation status (see
[`TRUSTED.md`](TRUSTED.md) for the full table and caveats):

- ✅ **Proved**: V1 (canonical-form invariant), V2 (overflow safety), V3
  (value correctness vs. the ghost model), V5 (GCD correctness +
  termination), V6 (algebraic laws), and R1 of V4 (identity on
  representables).
- 🟡🔴 **Not proved**: R2-R4 of V4 (the directed-rounding algorithm's
  directedness, error bound, and monotonicity -- the hardest single piece),
  and V7/V8 (spec-marked SHOULD).

Two important caveats on the proved items, detailed in `TRUSTED.md`: the
proofs live in standalone `verus/*.rs` files that mirror the shipped `src/`
code rather than verifying the literal compiled crate (wiring up `vstd` as
a real cargo dependency so both are the same code is unfinished work), and
every proof was authored and iterated on **entirely via CI feedback** --
the environment writing this crate has no local Verus toolchain access
(GitHub release-binary distribution; this session's GitHub access was
scoped to a single repository).

What backs the unproved obligations in the meantime: `overflow-checks =
true` in every build profile (any place a "provably in range" claim is
wrong fails loudly, not silently), and three test suites -- property tests
(`tests/property.rs`), a differential oracle against `malachite-q`
(`tests/differential.rs`), and adversarial edge cases
(`tests/adversarial.rs`) -- that empirically validate them, including R3's
`2^-60` error bound and R4's monotonicity. That's testing, not proof; treat
the `requires`/`ensures`-style doc comments on unproved obligations as a
precise target for future Verus work, not a substitute for it.
`cargo clippy -D warnings` and `cargo fmt --check` are clean throughout.

## What `Q` is

```rust
pub struct Q { /* num: i64, den: i64, private */ }
```

`value == num / den`, always in canonical form:
- **I1:** `den > 0`, `gcd(|num|, den) == 1`, `num == 0 => den == 1`.
- **I2:** `|num| <= 2^62 - 1` and `den <= 2^62 - 1`.

Canonical form means structural equality is mathematical equality, so `Q`
derives `Eq`, `Hash`, and implements a real total `Ord` (an upgrade over
`f64`'s `PartialOrd`) via `i128` cross-multiplication. It's a plain `Copy`
128-bit value type -- no heap, trivially `Send + Sync`.

### The rounding contract

Every arithmetic op computes its exact result in `i128` (safe: worst-case
intermediate for add/sub is `< 2^125`, for mul `< 2^124`, comfortably under
`i128`'s `2^127` ceiling given `I2`-bounded inputs -- see `src/ops.rs`).
If the gcd-reduced exact result fits `I2`, it's returned **exactly** --
**R1**: any computation whose exact values all fit the budget is
end-to-end exact, with zero rounding. Otherwise it's snapped to the
nearest (or, via `from_f64_dir`'s `Dir` parameter, a directed) dyadic
fraction `k / 2^s`, with an error bound of `|result - exact| <= 2^-60 *
max(1, |exact|)` (**R3**) and directed rounding bracketing the exact value
(**R2**). See `src/rounding.rs` module docs for the full algorithm
(binary long division, chosen specifically to avoid the overflow a naive
`num << s` would hit).

**Honesty consequence, stated plainly:** `add`/`mul` are commutative
unconditionally, but **not associative in general** once rounding kicks
in -- only on the exact path. Don't assume otherwise; `tests/property.rs`
checks associativity only for small, guaranteed-exact inputs.

### Magnitude ceiling (a clarification beyond the original spec)

`I2`'s `|num| <= 2^62 - 1` bound turns out to cap *magnitude*, not just
precision -- a value's magnitude is a lower bound on `|num|` for any valid
denominator. If an op's exact mathematical result exceeds that magnitude
(e.g. multiplying two near-`2^62` values), no `Q`, rounded or not, can
represent it even approximately. This crate **saturates** to `±(2^62-1)/1`
in that case rather than panicking or wrapping; see `src/rounding.rs` and
`tests/adversarial.rs::magnitude_ceiling_saturates_instead_of_panicking`.
The spec's own sizing analysis says the consuming engine never approaches
this ceiling (opinion values stay in `[0, 1]`), so treat this as a
documented theoretical edge, not a day-to-day concern.

## API surface

```rust
use the_q::{Q, Dir};

let a = Q::from_decimal(85, 2).unwrap();      // 0.85, exact
let b = Q::new(1, 3).unwrap();                // 1/3
let sum = the_q::add(a, b);                   // or `a + b`
let approx = the_q::from_f64_dir(0.1, Dir::Nearest).unwrap();

assert!(a.in_unit_interval());
```

Constructors: `zero`, `one`, `from_int`, `new`, `from_decimal`,
`from_f64_dir`. Arithmetic: `add`, `sub`, `mul`, `div`, `neg`, `abs`,
`recip`, `min`, `max`, `clamp` (also available as `+ - * / -` operator
overloads, an ergonomic addition beyond the spec's named-function
surface). Predicates: `is_zero`, `is_one`, `signum`, `in_unit_interval`,
full `Ord`. Conversions: `to_f64` (the one trusted boundary -- see
`TRUSTED.md`), `Display`, `serde` (feature `serde`, exact `(num, den)`
round-trip). N-ary: `sum`, `product`, `weighted_mean`.

`div`/`recip` panic on a zero divisor and `clamp` panics on `lo > hi` --
these are documented preconditions that, in the spec's Verus-checked
design, would be statically discharged by the caller; absent that proof,
this crate enforces them as hard runtime panics (in every build profile)
rather than silently producing an invalid `Q`.

### `QI`: directed-rounding intervals (spec M6, stretch)

```rust
use the_q::{interval_ops, Q, QI};

let a = QI::from_f64(0.1).unwrap();
let b = QI::point(Q::new(1, 3).unwrap());
let sum = interval_ops::add(a, b); // sum.lo() <= exact value <= sum.hi(), always
```

`QI { lo, hi }` brackets an exact rational value using the same `Dir`
plumbing the rounding design was built to support: every op rounds `lo`
down and `hi` up, so the true result is always inside `[lo, hi]`. `mul`/
`div` use the standard four-corners/reciprocal-interval constructions (see
`src/interval.rs`). No Verus proof of soundness -- plain Rust, tested
against `malachite-q` in `tests/interval.rs`; the spec marks this milestone
stretch.

## Why not just use `malachite-q` (or `f64`)?

- `f64` fusion arithmetic is non-deterministic across evaluation order,
  non-associative in a way nobody bounds, and unverifiable.
- `malachite-q` (the best available Rust bignum rational) is
  LGPL-3.0-only, which blocks static linking into proprietary binaries,
  and -- more fundamentally -- feeding *any* external crate's arithmetic
  into a Verus proof means trusting it as an unverified axiom. There is no
  verified bignum or rational anywhere in the Verus ecosystem as of this
  writing; that's the gap this crate exists to fill.
- Full arbitrary-precision rationals were also rejected: worst-case
  denominator growth in the consuming engine (~1000 sequential fusions)
  produces exact denominators hundreds to thousands of bits wide, and a
  *verified* bignum is an order-of-magnitude larger project than a
  bounded type with proven rounding.

`malachite-q` is used here **only** as a `[dev-dependencies]` oracle for
differential testing -- never in the shipped dependency tree. That's
enforced mechanically: run `./scripts/check-no-lgpl3-release-deps.sh`
(also wired into CI) to verify no LGPL-3.0 crate is reachable from the
release build graph.

## Out of scope

No transcendental functions (`exp`, `ln`, `pow` with rational exponent,
`sqrt`) and no arbitrary precision. Both are explicit non-goals of the
design this crate implements -- see the design doc's §2.6.

## Development

```sh
cargo build --all-targets --all-features
cargo test --all-features
cargo clippy --all-targets --all-features -- -D warnings
cargo fmt --check
./scripts/check-no-lgpl3-release-deps.sh

# Verus proofs (verus/*.rs, standalone -- see TRUSTED.md). Requires the
# verus binary on PATH; CI downloads it fresh each run (see ci.yml).
for f in verus/*.rs; do verus --rlimit 60 "$f"; done
```

## Design provenance

This crate implements milestones M1-M5 of a design spec for a "verified
rational arithmetic core" numeric backbone: the canonical `Q` type,
i128-safe arithmetic, directed dyadic rounding, the f64 boundary, n-ary
folds, serde (M1-M4), and the malachite-oracle/property-test/CI harness
(M5). M6 (stretch: Lipschitz lemmas, an interval type) is partially done --
`QI` is implemented and tested, the Lipschitz lemmas (V7) are not attempted.
See `TRUSTED.md` for exactly which of the spec's V1-V8 Verus obligations
are machine-proved vs. still open at any given commit.
