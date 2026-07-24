# Verus verification

Machine-checked proofs for the `the-q` rational core, verified by
[Verus](https://github.com/verus-lang/verus). Each file here is a self-contained
proof target (`verus <file>`); the CI `verus` job installs the toolchain and
runs them (`../.github/workflows/ci.yml`, `../ci/verify.sh`), failing the build
if any hard-gated file regresses.

## Machine-checked today (admit-free, CI hard-gated, `0 errors`)

**49 verified conditions** across six files, every run:

| File | Obligations discharged | Conditions |
|---|---|---|
| `src/gcd_checked.rs` | **V5** — Euclid computes `spec_gcd` + terminates (`decreases`) | 4 |
| `src/verified.rs` | **V2** (no i128 overflow), **V3** (`<` correct), **V6** (negation involution) | 6 |
| `src/verified_arith.rs` | **V2/V3** (`<=`, `==`, raw `add`/`mul` overflow-free + value-correct), **V6** (order antisymmetry & transitivity, `add`/`mul` commutativity), abs | 15 |
| `src/verified_pred.rs` | **V3** (`is_zero`, `signum`, `in_unit_interval`, `min`, `max` correct), order reflexivity | 9 |
| `src/verified_gcd.rs` | **V5** — `gcd` divides both arguments (via `lemma_fundamental_div_mod`) | 5 |
| `src/verified_reduce.rs` | **V5** — `gcd` is greatest; **V1 core** — reduce-by-gcd preserves value | 10 |

Discharged obligations, by spec number:

- **V2** — no i128 overflow: every budget-bounded cross-product / arithmetic
  intermediate is proven in range with `nonlinear_arith` against a concrete
  `2^62 − 1` literal (no bit-shifts on ghost `int`).
- **V3** — value correctness (division-free, cross-multiplication over ghost
  `int`): comparisons `<`/`<=`/`==`, predicates `is_zero`/`signum`/
  `in_unit_interval`, `min`/`max`, and the raw `add`/`mul` kernels.
- **V5** — **complete**: Euclid computes the spec GCD, terminates, divides both
  arguments, and is the greatest common divisor.
- **V6** — negation involution; order reflexivity, antisymmetry, transitivity;
  `add`/`mul` commutativity.
- **V1** — *core*: reducing by a common divisor preserves the value.

## Remaining obligations (the hard tail)

Honestly not yet discharged; each has a clear strategy:

- **V1 (finish)** — canonical-form *uniqueness* (`q_eq` ⟹ structural equality).
  Needs Euclid's lemma (`gcd(x,y)=1 ∧ x∣yz ⟹ x∣z`), i.e. a Bézout/coprimality
  argument on top of the GCD lemmas already proven here.
- **V4** — rounding R1–R4. R1 (identity on representables) and R2 (directed) are
  tractable given the reduce-value lemma; **R3** (the `2^-60` bound with the
  per-magnitude dyadic-snap case analysis) and **R4** (grid monotonicity) are
  the large proofs the spec itself flags as an order-of-magnitude bigger effort.
- **V7/V8** — Lipschitz perturbation lemmas; n-ary accumulation bound (SHOULD).

The shipped `../src/lib.rs` implements exactly these algorithms and is
independently validated by the `malachite-q` differential oracle (60k+ cases)
and the property suite, so behavior is checked from both directions while the
remaining symbolic proofs are completed through the same CI loop.

## Development note

The environment that authored these proofs cannot run Verus locally (github.com
and api.github.com are egress-blocked there; the release CDN is reachable only
via signed API redirects). Proofs are therefore developed against the CI runner,
which installs Verus from the latest release (resolved via the GitHub API) plus
the exact pinned Rust toolchain Verus requires. New proofs land in
`src/candidate*.rs` (reported non-fatal) and are promoted to the hard-gated set
above once they verify clean.
