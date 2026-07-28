# Trusted boundary

Per spec §5/§6: this file enumerates every function whose correctness is
*assumed* rather than proven, together with what's assumed and how it's
tested instead.

## Formal verification status (read this first)

**Verus is wired into CI** two ways: the `verus` job checks the standalone
proof files under `verus/*.rs`, and the `verus-real-code` job runs Verus
directly against `src/lib.rs` -- `vstd` is a real (non-optional) `[dependencies]`
entry, and `canonicalize_i128`/`gcd_u128` in `src/rounding.rs` carry inline
`verus!{}` annotations checked against the literal shipped code, not a
mirror. Current status, obligation by obligation:

| Obligation | Status | File |
|---|---|---|
| V1 (type invariant: canonical form) | ✅ proved, **for real code**: `canonicalize_i128`'s result is `I1`-canonical | `src/rounding.rs`; also `verus/gcd.rs` (`lemma_reduced_is_coprime`, mirror) |
| V2 (overflow safety) | ✅ proved | `verus/overflow_safety.rs` (mirror only) |
| V3 (value correctness vs ghost model) | 🟡 partial, **for real code**: `canonicalize_i128` proved value-preserving (cross-multiplication) | `src/rounding.rs`; full op-level value correctness only in `verus/value_correctness.rs` (mirror) |
| V4 (rounding contract R1-R4) | 🟡 partial: **R1** (identity on representables) proved | `verus/rounding_r1.rs` (mirror only). **R2/R3/R4** (directedness, the `2^-60` error bound, monotonicity -- i.e. `round_to_budget` itself) not attempted, real code or mirror |
| V5 (GCD correctness + termination) | ✅ proved, **for real code**: `gcd_u128` itself | `src/rounding.rs`; also `verus/gcd.rs` (mirror) |
| V6 (algebraic laws) | ✅ proved | `verus/algebra.rs` (mirror only; commutativity, associativity/distributivity on the exact path, neg/recip involutions, abs idempotence) |
| V7 (Lipschitz lemmas) | ✅ proved (spec-marked SHOULD) | `verus/lipschitz.rs` (mirror only) |
| V8 (n-ary fold error bounds) | ✅ proved (spec-marked SHOULD) | `verus/nary_bounds.rs` (mirror only) |

Two structural caveats:

1. **Most proofs are still standalone mirrors, not the literal shipped
   binary.** `canonicalize_i128` and `gcd_u128` are the only functions
   verified against the real `src/` source (via the `verus-real-code` CI
   job, `vstd` as a genuine cargo dependency). Everything else (`V2`,
   `V4`/R1, `V6`, `V7`, `V8`, and the op-level parts of `V3`) is still only
   checked via the independent mirror files under `verus/`, each re-stating
   the relevant formula/algorithm from `src/` (e.g. `verus/gcd.rs`'s
   `gcd_exec` mirrors `gcd_u128`) and proving it correct on its own terms.
   A manual read-through confirms the mirrored code matches the shipped
   code at the time of writing, but there is no automated check enforcing
   they stay in sync for the still-mirror-only obligations -- migrating
   them to real-code annotations (like `canonicalize_i128`/`gcd_u128`
   already are) closes that gap incrementally, one function at a time.
2. **Authored and iterated on via both CI feedback and (for the real-code
   push) local Verus toolchain access** (this session confirmed local
   network access to `verus-lang/verus`'s git repo and release binaries
   works, contrary to earlier assumptions baked into this file). The
   commit history shows real iteration (e.g. the first GCD attempt got
   10/12 verification conditions right, a follow-up fixed the remaining 2;
   `algebra.rs`'s polynomial identities needed the SMT `--rlimit` raised
   past the default; `canonicalize_i128` needed a documented Verus quirk
   worked around -- see the comments at its final `assert`s in
   `src/rounding.rs` -- where a fact proven about an if/else expression's
   arms didn't reliably connect back to a tuple-returning function's
   postcondition without an explicit restatement immediately before the
   `return`).

What backs the *unproved* obligations (R2-R4 of V4, and the op-level half of
V3) in the meantime: every contract is still documented as a precise
doc-comment contract at its function, `overflow-checks = true` in every
build profile means overflow bugs fail loudly rather than silently, and the
property/differential/adversarial test suites (`tests/`) empirically
validate them, including the `2^-60` error bound (R3) against the
`malachite-q` oracle and monotonicity (R4) via property tests. That is real,
but it is testing, not proof -- do not represent V4(R2-R4) as Verus-verified.

`QI` (the interval type, spec M6/stretch) has **no Verus proof at all** --
it's plain Rust, tested (`tests/interval.rs`) against the `malachite-q`
oracle for enclosure soundness, and the spec itself marks M6 as stretch.

## Trusted (`external_body`) functions

| Function | File | What's assumed | How it's tested |
|---|---|---|---|
| `to_f64` | `src/convert.rs` | IEEE-754 division rounding (`num as f64 / den as f64`) faithfully approximates the exact rational. Never fed back into `Q` arithmetic. | `tests/differential.rs`, `tests/adversarial.rs::to_f64_never_fed_back_is_documented_boundary` |
| `i128::unsigned_abs` | `src/rounding.rs` (`assume_specification`) | `vstd` doesn't model this std method natively; the trusted bridge asserts it returns `\|x\|` as a `u128`, exactly matching its documented std behavior. | `tests/property.rs`'s `I2`-invariant checks exercise every code path through it |

`to_f64` and the `unsigned_abs` bridge are the only trusted assumptions in
the *shipped crate*. `from_f64_dir` is **not** trusted: every finite `f64`
decomposes exactly into `mantissa * 2^exp` for integer `mantissa`/`exp`
(`src/convert.rs::decompose`), so the conversion is plain, exact integer
arithmetic funneled through the same `rounding::from_exact_i128` every
arithmetic op uses -- no float reasoning enters the computation at all.

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

1. Prove R2-R4 of V4 (`round_to_budget`'s directedness, error bound,
   monotonicity) -- the single hardest remaining spec gap, involving the
   `bitlen_u128`/binary-long-division algorithm's loop invariants. Not yet
   attempted against real code or a mirror.
2. Migrate the remaining mirror-only obligations (V2, V4/R1, V6, V7, V8,
   and the op-level half of V3) to real-code annotations in `src/`, the way
   `canonicalize_i128`/`gcd_u128` already are, one function at a time --
   closing structural caveat 1 above for the rest of the crate.
