# Trusted boundary

Per spec §5/§6: this file enumerates every function whose correctness is
*assumed* rather than proven, together with what's assumed and how it's
tested instead.

## Formal verification status (read this first)

**No Verus proof has been run against this codebase.** The spec calls for
machine-checked discharge of obligations V1-V8 via Verus. This
implementation was built in a sandboxed environment with no path to install
the Verus toolchain: Verus ships only as GitHub release binaries, and this
session's GitHub access is scoped to a single repository, with
`github.com`/`codeload.github.com`/release-asset hosts all rejecting
requests outside that scope. `cargo build`/`cargo test` work normally
(crates.io is unrestricted); Verus specifically could not be fetched.

Consequently:

- Every obligation below marked "V1".."V8" is a **documented, tested
  contract**, not a machine-checked one. Contracts are stated as doc
  comments next to the relevant code, cross-checked at runtime via
  `debug_assert!` where practical, and validated empirically by the
  property/differential/adversarial suites in `tests/`.
- The arithmetic core (`rounding.rs`, `q.rs`, `ops.rs`) is written to be
  Verus-annotation-ready: pure functions, no hidden state, explicit
  preconditions stated in prose at each `assert!`/`debug_assert!` site,
  division-free comparison (cross-multiplication, matching the spec's
  ghost-model discipline). Turning the doc comments into actual
  `requires`/`ensures` clauses and closing the proof is the concrete next
  step for whoever has Verus installed -- it was not fabricated here.
- Overflow safety (V2) is backed by `overflow-checks = true` in *both*
  dev and release profiles (`Cargo.toml`), so any place the "provably in
  range" claim is wrong fails loudly (a panic) instead of silently
  wrapping, in every build. This is a real safety net, just not a proof.

Do not represent this crate as Verus-verified until that gap is closed.

## Trusted (`external_body`) functions

| Function | File | What's assumed | How it's tested |
|---|---|---|---|
| `to_f64` | `src/convert.rs` | IEEE-754 division rounding (`num as f64 / den as f64`) faithfully approximates the exact rational. Never fed back into `Q` arithmetic. | `tests/differential.rs`, `tests/adversarial.rs::to_f64_never_fed_back_is_documented_boundary` |

That is the only trusted function in the crate. `from_f64_dir` is
**not** trusted: every finite `f64` decomposes exactly into
`mantissa * 2^exp` for integer `mantissa`/`exp` (`src/convert.rs::decompose`),
so the conversion is plain, exact integer arithmetic funneled through the
same `rounding::from_exact_i128` every arithmetic op uses -- no float
reasoning enters the computation at all.

## Rules enforced

- Zero `unsafe`, zero `assume`/`admit`-equivalent, anywhere in `src/`.
- `malachite-q` (the differential-test oracle, LGPL-3.0-only) is a
  `[dev-dependencies]`-only dependency. `scripts/check-no-lgpl3-release-deps.sh`
  fails CI if it (or any other LGPL-3.0 crate) ever appears in the
  non-dev dependency tree.
