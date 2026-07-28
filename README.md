# the-q

**Verified bounded rational arithmetic** — a standalone Rust crate, checked by
[Verus](https://github.com/verus-lang/verus), providing
exact-with-verified-rounding rational arithmetic (`Q = num/den` over `i64`).
Built as the numeric backbone for a subjective-logic fusion engine, and — as
far as we know — the first machine-checked rational arithmetic core in the
Verus ecosystem.

## The type

```rust
pub struct Q { num: i64, den: i64 }   // value = num / den
```

Invariants, proven preserved by **every** public operation (V1):

- **I1 (canonical):** `den > 0`, `gcd(|num|, den) == 1` — so structural
  equality *is* mathematical equality (proven: `lemma_canonical_unique`),
  and `Eq`/`Ord`/`Hash` are semantically correct.
- **I2 (bounded):** `|num| ≤ 2^62 − 1`, `den ≤ 2^62 − 1` — so every
  intermediate fits `i128` exactly and **no overflow or panic is possible**
  (proven with overflow checks on; V2).

## The rounding contract (V4)

Arithmetic is exact in `i128`, GCD-reduced, then:

- **R1 — identity on representables:** if the exact reduced result fits the
  budget, you get it *exactly*. Consequence (proven,
  `theorem_exact_path`): computations whose exact values all fit are
  end-to-end exact. Small investigations pay zero rounding.
- **R2 — directed:** `Dir::Down` result ≤ exact ≤ `Dir::Up` result. Plain
  ops use `Dir::Nearest` (ties away from zero).
- **R3 — error bound:** `|result − exact| ≤ 2^-60 · max(1, |exact|)`
  (B = 60), proven for every op.
- **R4 — monotone (per grid):** proven at the shared-scale level
  (`lemma_mag_round_monotone`), all three modes.

Implementation: dyadic snap onto `k / 2^s` with the scale chosen per
magnitude; `k` is found by **binary search over exact wide comparisons**
(no division, no error analysis — every step is an exact 192-bit integer
compare). Out-of-range magnitudes (`|x| > 2^62 − 1`, unreachable for the
consuming engine's [0, 1]-valued opinions) saturate at `±MAX/1`; R2/R3 are
conditional on being in range.

## Honesty note: associativity

With rounding, `add`/`mul` are **commutative** (proven, bit-exact:
`theorem_add_comm`, `theorem_mul_comm`) but **not associative in
general**. Associativity and distributivity are proven **on the exact
path** (`theorem_add_assoc_exact`, `theorem_mul_assoc_exact`,
`theorem_distrib_exact`). Order-independence claims built on this crate
therefore hold exactly for in-budget computations and up to the
accumulated `k · 2^-60` bound in general. Unlike `f64`, results are
deterministic and bit-exact reproducible for a fixed evaluation order.

## Surface

- Constructors: `zero`, `one`, `from_int`, `new(num, den)` (exact, never
  rounds), `from_decimal(mantissa, places)` (exact decimal ingestion),
  `from_f64_dir(v, dir)` (verified bit-decomposition; NaN/∞ → `None`).
- Arithmetic: `add/sub/mul/div` (+ `_dir` directed variants), `neg`, `abs`,
  `recip`, `min/max/clamp` — division by zero is a *precondition*,
  discharged statically, never a runtime panic.
- Comparison: exact `eq/lt/le/cmp` via `i128` cross-multiplication; `Ord`
  is a total order agreeing with the ghost order.
- Predicates: `is_zero`, `is_one`, `signum`, `in_unit_interval`.
- n-ary: `sum`, `product`, `weighted_mean`, `int_pow` (fixed-order folds).
- Intervals: `QI = [lo, hi]` on the directed modes (`add`/`sub`/`neg`,
  `mul_nonneg`), with proven enclosure of exact results
  (`lemma_qi_add_encloses`, `lemma_qi_mul_encloses`).
- Out: `to_f64` (trusted, display only — see `TRUSTED.md`), `Display`
  (`"num/den"`), `serde` (feature `serde`; exact `(num, den)` round-trip).

Note one deliberate deviation from the original spec sheet: `Q::new`
returns `None` not only for `den == 0` but also for the case where the
reduced value exceeds the I2 budget — e.g. `Q::new(i64::MAX, 1)`.
Rejecting is safer than silently rounding in an "exact" constructor. Same
for `from_decimal`; `i64::MIN` is handled correctly via `u128` and
accepted iff the reduced form is in budget.

## Verification

```
verification results:: 389 verified, 0 errors
```

Beyond the MUST-tier obligations (V1-V6), the SHOULD tier is delivered
too: **V7** error-propagation (Lipschitz) lemmas for add/sub/mul/recip/div
(`src/lipschitz.rs`, the enabling layer for the interval type), and **V8**
accumulated-error theorems for the n-ary folds (`src/accumulate.rs`):
`sum` is within `k*w*2^-59` of the exact sum whenever the exact partial
sums are bounded by `w`, and `product` over unit-interval elements is
within `k*2^-59` of the exact product — both wired into the exec fns'
`ensures`. The M6 stretch interval type `QI` ships as well
(`src/interval.rs`).

- Zero `assume`/`admit`. Trusted surface: exactly one meaningfully trusted
  function (`to_f64`) plus a one-line `to_bits` model bridge — enumerated
  with backing tests in [`TRUSTED.md`](TRUSTED.md).
- Verify locally (needs [Verus](https://github.com/verus-lang/verus)
  release `0.2026.07.12` and Z3 4.12.5):
  `verus --crate-type=lib src/lib.rs --rlimit 30`
- Plain `cargo build` works on stable Rust (ghost code erases; `vstd` from
  crates.io).
- Tests: `cargo test` — differential oracle against
  [malachite-q](https://crates.io/crates/malachite-q) (**dev-dependency
  only**; it is LGPL-3.0 and never enters the release dependency tree — CI
  enforces this), property tests, adversarial fixtures.

## Design rationale (short)

Exact ℚ denominators grow without bound under fusion chains (hundreds of
bits at realistic depth), so full exactness needs bignum — but there is no
verified bignum in the Verus ecosystem, and unverified ones enter proofs
as axioms. The bounded-rational-with-verified-rounding design gives: exact
results while values fit a 2^62 budget (the common case: short-decimal
inputs, shallow chains), machine-checked `2^-60` relative error bounds when
they don't, determinism always. Worst-case accumulated error at production
scale (~2×10^4 sequential ops) is ~2×10^-14 relative — f64-class precision
with a *proven* bound instead of folklore.
