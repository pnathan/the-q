# Verus verification

Machine-checked proofs for the `the-q` rational core, verified by
[Verus](https://github.com/verus-lang/verus). Each file here is a self-contained
proof target (`verus <file>`); the CI `verus` job installs the toolchain and
runs them (`../.github/workflows/ci.yml`, `../ci/verify.sh`), failing the build
if any hard-gated file regresses.

## Status: all obligations V1–V8 discharged — on standalone transcriptions

**~106 verified conditions** across twelve admit-free files, `0 errors` every
run. No `assume`/`admit` anywhere in the hard-gated set.

> **Important scope note.** These files are **standalone transcriptions** of the
> algorithms — none of them is `../src/lib.rs`, and nothing yet enforces that a
> transcription agrees with its `src/lib.rs` counterpart (e.g.
> `verified_round.rs` vs. the exec `round_to_budget`). So each row below is
> "machine-checked *on a transcription*", not on the shipped code. Closing that
> gap (see "Remaining") is the work relevant to §6/§8 acceptance.

| File | Obligations | Conds |
|---|---|---|
| `gcd_checked.rs` | **V5** — Euclid computes `spec_gcd` + terminates | 4 |
| `verified.rs` | **V2** overflow, **V3** `<`, **V6** negation | 6 |
| `verified_arith.rs` | **V2/V3** `<=`/`==`/raw add·mul, **V6** order antisym+trans + commutativity, abs | 15 |
| `verified_pred.rs` | **V3** `is_zero`/`signum`/`in_unit_interval`/`min`/`max`, reflexivity | 9 |
| `verified_gcd.rs` | **V5** — `gcd` divides both (`lemma_fundamental_div_mod`) | 5 |
| `verified_reduce.rs` | **V5** — `gcd` greatest; **V1** — reduce preserves value | 10 |
| `verified_uniq.rs` | **V1** — Bézout, Euclid's lemma, canonical uniqueness | 22 |
| `verified_round.rs` | **V4** — R1 identity, R2 directed brackets, R3 grid error | 10 |
| `verified_round_mono.rs` | **V4** — R4 grid monotonicity | 5 |
| `verified_round_b60.rs` | **V4** — R3 `2^-60` magnitude tie-in (`pow2` additivity) | 10 |
| `verified_accum.rs` | **V8** — n-ary accumulation bound (`k·eps`) | 4 |
| `verified_lipschitz.rs` | **V7** — Lipschitz perturbation for add/mul | 6 |

Per spec obligation:

- **V1** ✅ — invariants; reduce-by-gcd preserves value; **canonical uniqueness**
  (value equality ⟹ structural equality) via Bézout + Euclid's lemma.
- **V2** ✅ — no i128 overflow anywhere (`nonlinear_arith` vs. a concrete
  `2^62 − 1` literal; no bit-shifts on ghost `int`).
- **V3** ✅ — division-free value correctness for comparison, predicates,
  min/max, and the raw add/mul kernels.
- **V4** ✅ — rounding **R1–R4**: identity on representables, directed floor/ceil
  bracketing, grid error `0 ≤ n·2^s − q·d < d` with the per-magnitude tie-in
  `1/2^s ≤ 2^-60·max(1,|v|)`, and grid monotonicity.
- **V5** ✅ — GCD: computes the spec, terminates, divides both, is greatest.
- **V6** ✅ — negation/abs; order reflexivity/antisymmetry/transitivity;
  add/mul commutativity.
- **V7** ✅ — Lipschitz perturbation bounds (add: triangle; mul: `m·(da+db)` on a
  bounded domain) — the enabling layer for a future interval type.
- **V8** ✅ — n-ary accumulation: `k` per-step errors within `±eps` sum to
  within `±k·eps`.

## Remaining — verify `src/lib.rs` itself (§6/§8-relevant)

The proofs are stated over the mathematical model (ghost `int`/`Seq`) in files
separate from the shipped crate. The open item is to make **`../src/lib.rs` the
verification target**: wire `vstd` as a dependency and move the
`requires`/`ensures` onto the exec functions themselves (start with
`reduce_i128` and `round_to_budget`, since everything funnels through them), so
CI machine-checks the code that actually ships rather than a copy of it. This is
proof effort on the same toolchain, not a redesign — a sibling approach verifies
the shipped crate directly with `verus --crate-type=lib src/lib.rs`.

Until then, agreement between each transcription and its `src/lib.rs` counterpart
is **not enforced by CI** — a later edit to an exec op would not fail the `verus`
job. What pins the shipped behavior today is the `malachite-q` differential
oracle (60k+ cases) plus the property/adversarial suite, which exercise
`src/lib.rs` end-to-end from the other direction.

## Development note

The environment that authored these proofs cannot run Verus locally (github.com
and api.github.com are egress-blocked there; the release CDN is reachable only
via signed API redirects). Proofs were therefore developed against the CI
runner, which installs Verus from the latest release (resolved via the GitHub
API) plus the exact pinned Rust toolchain Verus requires.
