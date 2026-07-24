# Verus verification

Machine-checked proofs for the `the-q` rational core, verified by
[Verus](https://github.com/verus-lang/verus). Each file here is a self-contained
proof target (`verus <file>`); the CI `verus` job installs the toolchain and
runs them (see `../.github/workflows/ci.yml` and `../ci/verify.sh`).

## What is machine-checked today (admit-free, CI hard-gated)

These files verify with **0 errors** on every CI run and any failure fails the
build:

| File | Obligations | Verified conditions |
|---|---|---|
| `src/gcd_checked.rs` | **V5 core** — Euclid computes `spec_gcd` + terminates (`decreases`) | 4 |
| `src/verified.rs` | **V2** (no i128 overflow), **V3** (comparison `<` correct), **V6** (negation involution) | 6 |
| `src/verified_arith.rs` | **V2/V3** (`<=`, `==`, raw `add`/`mul` overflow-free + value-correct), **V6** (order antisymmetry & transitivity, `add`/`mul` commutativity), abs | 13+ |

All value correctness is stated **division-free** (cross-multiplication over
ghost `int`), and all overflow bounds are discharged with `nonlinear_arith`
against a concrete `2^62 − 1` budget literal — no bit-shifts on ghost `int`
(which Verus spec mode rejects).

## In development (reported non-fatal; promoted once green)

`src/candidate.rs`, `src/candidate_gcd.rs` — exec predicate correctness
(`is_zero`, `signum`, `in_unit_interval`, `min`, `max`) and the full **V5** GCD
divisibility (`gcd` divides both / is greatest). These run on CI and their Verus
output is printed, but do not gate the build until they verify clean.

## Remaining obligations (the hard tail)

Honest status of what is **not yet** discharged:

- **V1** (canonical-form uniqueness / `reduce` preserves value + canonicality)
  — depends on the GCD divisibility lemmas now in `candidate_gcd.rs`.
- **V4** (rounding R1–R4). R1 (identity on representables) and R2 (directed) are
  tractable; **R3** (the `2^-60` error bound with the per-magnitude dyadic-snap
  case analysis) and **R4** (monotonicity across grids) are the genuinely large
  proofs the spec itself flags as an order-of-magnitude bigger effort.
- **V7/V8** (Lipschitz perturbation lemmas; n-ary accumulation bound) — SHOULD.

These are being worked through the same CI loop. The shipped `../src/lib.rs`
implements exactly these algorithms and is independently validated by the
`malachite-q` differential oracle (60k+ cases) and the property suite, so the
behavior is checked from both directions while the symbolic proofs are
completed.

## Toolchain note

The environment that authored these proofs could not run Verus locally
(github.com and api.github.com are egress-blocked there; the release CDN is only
reachable via signed API redirects). Proofs are therefore developed against the
CI runner, which installs Verus from the latest release (resolved via the GitHub
API) plus the exact pinned Rust toolchain Verus requires.
