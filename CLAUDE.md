# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What this crate is

`the-q` is a bounded rational arithmetic library in Rust whose specifications
and proofs are written in [Verus](https://github.com/verus-lang/verus) inside
`verus! { ... }` blocks in the source. Ghost code is erased by the macro, so
plain `rustc` builds the annotated sources unchanged; `cargo verus verify`
checks the proofs. Read `README.md` for the semantics, `VERIFICATION.md` for
the obligation map (V1–V10), `TRUSTED.md` for the three `external_body`
functions, `docs/SPEC.md` for the original specification.

## Commands

```sh
cargo build --locked --all-features
cargo test --locked --all-features            # also: --release (overflow checks stay on)
cargo test --test oracle                      # one suite
cargo test --test oracle -- rounding_r3       # one test, by substring
cargo clippy --locked --all-targets --all-features -- -D warnings
cargo fmt --check
cargo bench --bench arith                     # no criterion; prints its own quality block
cargo verus verify --locked --all-features -- --multiple-errors 8
```

`--multiple-errors` is not optional in practice: Verus reports one error per
function body by default, so a module with an early failure looks clean.

Repository-specific checks, all run in CI:

```sh
./scripts/check-no-lgpl.sh                        # malachite-q must stay dev-only
./scripts/check-rat-privacy.sh                    # Rat/QI fields unreachable downstream
python3 scripts/check-vacuous-theorems.py --self-test && \
python3 scripts/check-vacuous-theorems.py         # ensures that restate requires
```

Accuracy audit of the transcendentals against two external oracles (mpmath and
SBCL; both must be installed):

```sh
cargo test --release --test bounds dump_transcendentals -- --ignored
python3 scripts/accuracy/eval.py  target/accuracy-dump.tsv
sbcl --script scripts/accuracy/eval.lisp target/accuracy-dump.tsv
```

## Toolchain pinning

The Verus binary and the `vstd` / `verus_builtin` / `verus_builtin_macros`
crates are one unit; a mismatch is not guaranteed to fail loudly. `Cargo.toml`
states them as caret requirements so downstream crates can unify, and pinning
is done by the committed `Cargo.lock` plus `--locked` on every CI invocation.
`VERUS_VERSION` in `.github/workflows/ci.yml` and `Cargo.lock` are bumped
together. Verus is a rustc driver bound to one exact compiler version; CI reads
that version from the archive's `rust-toolchain.toml`. MSRV is 1.85, edition
2024.

## Architecture

Layers, innermost first. Each layer's proofs stand on the one below and add no
new rounding obligations.

* `types.rs` — the `Rat` struct (private `i64` fields), `Dir`, `MAX_MAG =
  2^62 − 1`. The budget is what makes cross-multiplied `i128` intermediates fit:
  products below `2^124`, sums below `2^125`.
* `model.rs` — the ghost model in unbounded `int`. Value specifications are
  **division-free**: "`r` is `a + b`" is `r.num * (a.den * b.den) == (a.num *
  b.den + b.num * a.den) * r.den`. Division appears only inside definitional
  spec functions (`gcd_nat`, `bitlen`, `grid_num`).
* `gcd.rs` — Stein's binary gcd; `gcd_u128` is the workhorse of canonicalisation.
* `round.rs` — `round_frac_exec`, the single canonicalising entry point every
  arithmetic operation funnels through, and R1–R4. `round_frac` is the total
  spec function it mirrors; operations ensure equality with *that function*, not
  merely with its properties, which is what makes commutativity and
  bit-determinism provable. `shift_div` computes `floor(n · 2^s / d)` without
  ever forming the `2^185` product.
* `saturation.rs` — one lemma recording that scoping R3 below the ceiling is a
  choice, not a necessity.
* `q.rs` — the public `Rat` API. Every operation computes its exact `i128` pair
  and hands it to `round_frac_exec`. `require_condition` turns preconditions
  (zero divisor, `lo > hi`) into runtime panics for unverified callers.
* `ext.rs` — `Q`, the total layer: `Number(Rat)`, `PosSat`/`NegSat`,
  `PosInf`/`NegInf`, `Nan`. A wrapper, not a rewrite; the kernel invariant is
  untouched. `PosSat` denotes finite reals above the budget, so `0 * PosSat ==
  0` and there is no `is_finite()`.
* `interval.rs` (`QI`), `nary.rs`, `lipschitz.rs`, `laws.rs` — corollary layers.
  `QI` gets enclosure free from R2 (lo rounds `Down`, hi `Up`). `nary` folds are
  fixed left folds, hence bit-reproducible across machines and threads.
* `fx.rs` — fixed-point `i128` kernel on a `2^-63` grid (two guard bits) used by
  `exp` and `ln`; no gcd, no canonical form per step.
* `transcendental.rs` — roots and transcendentals on `Q`. Fixed-length series,
  so termination is structural and cost is constant. Totality and termination
  are proven; **accuracy is measured, not proven**.
* `convert.rs` — the crate's edges: `f64` in and out, `Display`, `FromStr`,
  serde (feature-gated).

## Invariants to preserve when editing

* `Rat`'s and `QI`'s fields stay private. Public contracts use the closed spec
  accessors `n()` / `d()`, never the fields. `check-rat-privacy.sh` compiles a
  downstream probe that must fail.
* No `assume(...)`, no `admit()` in `src/`. Exactly three `external_body`
  functions exist (`f64_decompose`, `to_f64`, `q::require_condition`); adding a
  fourth means updating `TRUSTED.md` and justifying it.
* No `wrapping_*`, `saturating_*` or `unchecked_*` anywhere. `overflow-checks`
  is on in release as a second independent execution of the V2 claim.
* Every new arithmetic path routes through `round_frac_exec`; do not
  canonicalise by hand.
* New value specifications are division-free (see `model.rs`).
* A new `proof fn` whose `ensures` restates its `requires` proves nothing while
  raising the verified count. Run `check-vacuous-theorems.py`; fixtures for the
  linter live in `scripts/fixtures/vacuous`.
* `malachite-q` (LGPL-3.0-only) is the test oracle and must never leave
  `[dev-dependencies]`.
* Changing a proven bound, an accuracy figure, or the verified count means
  updating `README.md` and `VERIFICATION.md` in the same change; the numbers in
  those files are quoted as evidence and `tests/readme_examples.rs` compiles the
  README's code.

## Test suites

`tests/oracle.rs` differential against `malachite-q` (20 000 random cases per
operation per direction, plus every `p/q` with `|p|, q ≤ 12`);
`tests/bounds.rs` the nearest bound, weighted-mean bound and interval
enclosure; `tests/props.rs` the invariant, the laws, cross-thread byte
identity; `tests/adversarial.rs` budget edges and the two documented
counterexamples; `tests/transcendental.rs` accuracy against the recorded
oracles; `tests/readme_examples.rs` the README. `tests/common/mod.rs` holds the
oracle plumbing and `assert_wf`, which re-derives canonicality with an
independent gcd on every produced value.

## API stability

`Rat`, `Q`, `Dir`, `QI`, `Exact`, their operations and constructors, and `nary`
follow semver. `gcd`, `model`, `round`, `lipschitz`, `fx` and executable helpers such
as `round::round_frac_exec_with_gcd` are public only because Verus's visibility
rules demand it and may change shape in patch releases.

## Licence

AGPL-3.0-or-later, dual-licensed commercially. New files carry the same terms.
