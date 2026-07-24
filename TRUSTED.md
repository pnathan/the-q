# Trusted boundary

Per spec §5/§6: this file enumerates every function whose correctness is
*assumed* rather than proven, together with what's assumed and how it's
tested instead.

## Formal verification status (read this first)

**Verus is wired into CI** (`.github/workflows/ci.yml`, `verus` job) and is
machine-checking real proofs against `verus/*.rs`. Current status, obligation
by obligation:

| Obligation | Status | File |
|---|---|---|
| V1 (type invariant: canonical form) | ✅ proved | `verus/gcd.rs` (`lemma_reduced_is_coprime`) |
| V2 (overflow safety) | ✅ proved | `verus/overflow_safety.rs` |
| V3 (value correctness vs ghost model) | ✅ proved | `verus/value_correctness.rs` |
| V4 (rounding contract R1-R4) | 🟡 partial: **R1** (identity on representables) proved | `verus/rounding_r1.rs`. **R2/R3/R4** (directedness, the `2^-60` error bound, monotonicity -- i.e. `round_to_budget` itself) not attempted |
| V5 (GCD correctness + termination) | ✅ proved | `verus/gcd.rs` |
| V6 (algebraic laws) | ✅ proved | `verus/algebra.rs` (commutativity, associativity/distributivity on the exact path, neg/recip involutions, abs idempotence) |
| V7 (Lipschitz lemmas) | ❌ not attempted (spec-marked SHOULD) | -- |
| V8 (n-ary fold error bounds) | ❌ not attempted (spec-marked SHOULD) | -- |

Two structural caveats that apply to every proved item above:

1. **Standalone mirrors, not the literal shipped binary.** Every file under
   `verus/` is an independent Verus program, checked directly via
   `verus verus/<file>.rs`, and is *not* part of the `the-q` cargo package
   (see `verus/smoke_test.rs`'s header comment for why: getting `vstd` wired
   up as a real cargo dependency so the exact shipped source could be
   verified *and* still `cargo build` normally is unfinished work -- it
   requires a `vstd`/`builtin`/`builtin_macros` git dependency on
   `verus-lang/verus` that this environment cannot resolve locally either,
   so it's untested and was deliberately not attempted this pass). Each
   proof file re-states the relevant formula/algorithm from `src/` (e.g.
   `verus/gcd.rs`'s `gcd_exec` mirrors `gcd_u128`/`gcd_i64`) and proves it
   correct on its own terms. A manual read-through confirms the mirrored
   code matches the shipped code at the time of writing, but there is no
   automated check enforcing they stay in sync -- that's the concrete gap
   left by not having `vstd` as a real dependency.
2. **Authored and iterated on entirely via CI feedback.** The environment
   that wrote these proofs has no local Verus toolchain access (GitHub
   release-binary distribution; this session's GitHub access was scoped to
   this one repository). Every proof here was validated by pushing and
   reading back Actions logs, not locally. The commit history shows real
   iteration (e.g. the first GCD attempt got 10/12 verification conditions
   right, a follow-up fixed the remaining 2; `algebra.rs`'s polynomial
   identities needed the SMT `--rlimit` raised past the default).

What backs the *unproved* obligations (R2-R4 of V4, V7, V8) in the meantime:
every contract is still documented as a precise doc-comment contract at its
function, `overflow-checks = true` in every build profile means overflow
bugs fail loudly rather than silently, and the property/differential/
adversarial test suites (`tests/`) empirically validate them, including the
`2^-60` error bound (R3) against the `malachite-q` oracle and monotonicity
(R4) via property tests. That is real, but it is testing, not proof --
do not represent V4(R2-R4)/V7/V8 as Verus-verified.

`QI` (the interval type, spec M6/stretch) has **no Verus proof at all** --
it's plain Rust, tested (`tests/interval.rs`) against the `malachite-q`
oracle for enclosure soundness, and the spec itself marks M6 as stretch.

## Trusted (`external_body`) functions

| Function | File | What's assumed | How it's tested |
|---|---|---|---|
| `to_f64` | `src/convert.rs` | IEEE-754 division rounding (`num as f64 / den as f64`) faithfully approximates the exact rational. Never fed back into `Q` arithmetic. | `tests/differential.rs`, `tests/adversarial.rs::to_f64_never_fed_back_is_documented_boundary` |

That is the only trusted function in the *shipped crate*. `from_f64_dir` is
**not** trusted: every finite `f64` decomposes exactly into
`mantissa * 2^exp` for integer `mantissa`/`exp` (`src/convert.rs::decompose`),
so the conversion is plain, exact integer arithmetic funneled through the
same `rounding::from_exact_i128` every arithmetic op uses -- no float
reasoning enters the computation at all.

Within the `verus/` proof files: `verus/rounding_r1.rs::round_to_budget_stub`
is marked `#[verifier::external_body]` and deliberately unmodeled -- it
stands in for `round_to_budget` so `from_exact_pair` structurally mirrors
the real `from_exact_i128`'s if/else shape, without claiming anything about
R2-R4 (which that file doesn't attempt).

## Rules enforced

- Zero `unsafe`, zero `assume`/`admit`-equivalent, anywhere in `src/`.
- `malachite-q` (the differential-test oracle, LGPL-3.0-only) is a
  `[dev-dependencies]`-only dependency. `scripts/check-no-lgpl3-release-deps.sh`
  fails CI if it (or any other LGPL-3.0 crate) ever appears in the
  non-dev dependency tree.

## Concrete next steps (in priority order)

1. Wire `vstd`/`builtin`/`builtin_macros` as real dependencies so the
   *literal* `src/` code is what Verus checks (closing caveat 1 above),
   rather than a manually-kept-in-sync mirror.
2. Prove R2-R4 of V4 (`round_to_budget`'s directedness, error bound,
   monotonicity) -- the single hardest remaining piece, involving the
   `bitlen_u128`/binary-long-division algorithm's loop invariants.
3. V7 (Lipschitz lemmas) and V8 (n-ary bound) -- spec-marked SHOULD.
