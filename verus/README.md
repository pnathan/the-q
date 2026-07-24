# Verus verification scaffold

This directory holds the [Verus](https://github.com/verus-lang/verus)
specification and proof scaffold for the `the-q` rational core. It is a
**separate compilation unit from the shipped crate**: `../src/lib.rs` is the
executable, `cargo`-buildable implementation; the files here mirror that
implementation with Verus `spec`/`proof`/`requires`/`ensures` annotations so the
integer arithmetic can be machine-checked.

## Status (honest accounting)

Verus could **not be installed in the environment that authored this scaffold**
(its releases are fetched from GitHub, which the sandbox egress proxy blocks, and
`z3` was absent), so **the proofs here have not yet been machine-checked**. They
are written to Verus discipline and are structured for a session that has the
toolchain to discharge. Each proof obligation is annotated with its status:

| Obligation | File / item | State |
|---|---|---|
| V5 GCD correctness + termination | `src/gcd.rs` | complete spec + proof, ready to check |
| V1 invariants I1∧I2 | `src/model.rs` `wf()` + per-op `ensures` | specs complete; preservation proofs structured |
| V2 no overflow (i128 in range) | `src/arith.rs` overflow lemmas | bounds lemmas written; ready to check |
| V3 value correctness (division-free) | `src/model.rs` `q_eq/q_le` + per-op `ensures` | specs complete; add/mul/cmp proofs structured |
| V4 rounding R1–R4 | `src/round.rs` | contract stated as `ensures`; R1 proof structured, R2–R4 skeleton |
| V6 algebraic laws | `src/laws.rs` | statements complete; commutativity proof structured |

**No `assume`/`admit` appears in any obligation that is marked "complete".**
Structured/skeleton obligations use explicit `// OBLIGATION:` markers where a
proof step is still owed — they are *not* silently admitted. The shipping-code
rule (zero `assume`/`admit`) applies to obligations promoted to "complete".

## How to check (once the toolchain is available)

```sh
# Install verus per https://github.com/verus-lang/verus (needs z3).
verus verus/src/lib.rs
```

`ci/verify.sh` wraps this and is invoked by `.github/workflows/ci.yml`; the CI
job is currently marked `continue-on-error` until the proofs are all promoted to
"complete", so a green `cargo` build/test is the enforced gate today and the
`verus` job reports progress without blocking.

## Why the design is Verus-friendly

- **Division-free specs.** Value correctness is stated by cross-multiplication
  over ghost `int` (`q_eq(a,b) := a.num*b.den == b.num*a.den`), never SMT
  division — the single most important choice for `z3` stability.
- **`2^62` budget, `i128` intermediates.** Every intermediate is proven `<
  2^127` from I2, so overflow checking discharges mechanically (V2).
- **Dyadic-snap rounding.** The grid `p / 2^s` gives a direct, closed-form error
  bound for R3, avoiding the loop-invariant/termination burden of a
  Stern–Brocot best-approximant.
