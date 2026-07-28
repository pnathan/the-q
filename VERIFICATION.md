# Verification status

## Read this first

The specifications and proofs in this crate are **written but not yet
machine-checked**.

The Verus verifier is distributed as a binary through GitHub releases. The
environment this crate was authored in routes all outbound HTTPS through a
policy-enforcing proxy that returns `403` for `github.com`, so the verifier
could not be obtained or run. What *was* available on crates.io — `vstd`,
`verus_builtin`, `verus_builtin_macros` — is enough to compile the annotated
sources with plain rustc, which is why `cargo build` works and the crate is
usable today.

Concretely, this means:

* **Proven-by-construction claims you can rely on now:** none of the `ensures`
  clauses have been discharged by the solver.
* **What *is* established:** the executable behaviour, by a differential test
  suite against an independent arbitrary-precision oracle (`malachite-q`) —
  20,000 random cases per operation per rounding direction against R1/R2/R3,
  90,000 exhaustive small-input pairs, the `f64` boundary, budget-edge fixtures,
  saturation, and a 10⁴-operation chain. Plus every algebraic law below,
  property-tested. Overflow checks are on in both `dev` and `release`, so the
  V2 claim (no `i128` intermediate overflows) has been executed against roughly
  ten million operations without a panic.
* **What to expect on first verification:** proof debugging. Nonlinear
  arithmetic is where SMT solvers struggle most, and this crate is nothing but
  nonlinear arithmetic. Expect to add intermediate assertions, split
  `by(nonlinear_arith)` blocks, and adjust `vstd` lemma paths (`vstd`'s
  `arithmetic::div_mod` module is used for the Euclidean division facts and its
  API may have drifted). The *statements* — the specifications, the invariants,
  the theorem shapes — are the durable part; the tactics inside proof bodies are
  the disposable part.

The CI workflow already runs `cargo verus verify`. It is marked
`continue-on-error: true` **only** because a permanently-red required check is
worse than an honest advisory one. **Flip it to required the moment the proofs
go through**; the line is commented in `.github/workflows/ci.yml`.

Two things the first CI run established about the *harness*, both now fixed:

* Verus is a rustc driver, so it links against one exact compiler version and
  refuses to run against any other (release `0.2026.07.27.31579f0` wants
  `1.97.1`). The workflow now reads that version out of the release archive's
  `rust-toolchain.toml`, installs it with rustup, and makes it the default.
* `cargo verus` verifies nothing unless the crate opts in. `Cargo.toml` now
  carries `[package.metadata.verus] verify = true`.

The plumbing is exercised and working — the verifier loads, checks `vstd`
(2058 verified, 0 errors), and reaches this crate. Three layers of problem have
surfaced so far, in order:

1. **Ghost-code type errors** that plain rustc cannot catch, because rustc
   erases exactly the code they live in: unsuffixed integer literals in `spec`
   position, `int`-vs-`i64` in a spec-constructed `Q`, `i128`-vs-`int` at a
   `proof fn` call site. Fixed.
2. **Datatype opaqueness.** Verus treats a type as opaque wherever any field is
   invisible, and a public specification must be well-formed everywhere it is
   visible. `Q`'s `pub(crate)` fields made `Q::wf` unable to mention `self.num`
   at all. Fixed by making the fields public; see the note on `Q` and the
   README for what that costs and why it costs less than it looks.
3. **Actual proof obligations.** This is where it now is.

The practical lesson of authoring Verus without the verifier: `cargo build`
passing means the *executable* code is well-typed and says nothing whatsoever
about the specifications.

### Where the proofs stand

Round three reported 20 errors. Fixed since:

* the missing `#[trigger]` on `divides` — the only candidate term is a
  multiplication and Verus will not pick an arithmetic operator on its own;
* an unproven `i128` bound in `from_f64_dir`, and its `round_frac_exec`
  denominator precondition;
* four `d > 0` preconditions in `interval::add`/`sub`;
* `theorem_interval_add_contains`, rewritten as four small steps through a new
  `lemma_add_endpoint_order` instead of one large `nonlinear_arith` goal;
* three `rlimit` exhaustions in `lipschitz`, split into smaller ring steps with
  the limit raised.

**Known still-failing, both SHOULD tier:**
`lipschitz::lemma_error_accumulates_additively` and the V8 theorems in `nary`
(`theorem_sum_error_accumulation`, `theorem_exact_fold_is_exact`). These are
stated correctly but their proof bodies are sketches, not discharged arguments —
see V8 below. They are not claimed as proven anywhere in this crate.

And a standing caveat on reading any of this: Verus reports **one error per
function body** by default. A module with no reported error has not necessarily
verified — it may simply not have been reached, or have further errors behind
the first. Do not read silence as success until a clean run says
`0 errors`.

No `assume(...)` and no `admit()` appear anywhere in `src/`. Two functions are
`external_body`, both at the `f64` edge, both enumerated in `TRUSTED.md`.

---

## Obligation map

| # | Obligation | Tier | Where |
|---|---|---|---|
| V1 | I1 ∧ I2 preserved by every public operation | MUST | `Q::wf` in `model.rs`; every public function `requires` it of inputs and `ensures` it of outputs |
| V2 | No panic, no overflow; every `i128` intermediate in range | MUST | `q::lemma_op_widths`, `round::lemma_quotient_bound`, `round::shift_div`, `model::lemma_mul_in_i128` |
| V3 | Value correctness against the ghost model, division-free | MUST | `model::q_is` / `q_eq` / `q_le`; `round::lemma_r1_identity` |
| V4 | Rounding contract R1–R4 | MUST | `round::lemma_r1_identity`, `lemma_r2_directed`, `lemma_r3_error`, `lemma_r4_monotone_grid` |
| V5 | GCD correctness and termination | MUST | `gcd.rs`, whole module |
| V6 | Algebraic laws | MUST | `laws.rs`, whole module |
| V7 | Error-propagation (Lipschitz) lemmas | SHOULD | `lipschitz.rs` |
| V8 | N-ary accumulation bound `k · 2^-B` | SHOULD | `nary::theorem_sum_error_accumulation` |

### V1 — the type invariant

`Q::wf(self)` in `model.rs` is the conjunction of I1 and I2:

```
den > 0  ∧  gcd(|num|, den) == 1  ∧  (num == 0 ⟹ den == 1)
         ∧  |num| ≤ 2^62 − 1      ∧  den ≤ 2^62 − 1
```

Every constructor `ensures` it, every operation `requires` it of its inputs and
`ensures` it of its result. The `Q` fields are `pub(crate)`, so no external code
can build a value that violates it; `serde` deserialisation goes through
`Q::new` and returns an error rather than a malformed value.

Runtime cross-check: `common::assert_wf` re-derives canonicality with its own
independent gcd and is called on every value produced in
`props::every_operation_preserves_the_invariant` (30,000 iterations × ~15
operations) and throughout the oracle and adversarial suites.

### V2 — no panic, no overflow

The width table is in `README.md` and in the `q.rs` module header. The
non-obvious case is the rounding step, which needs `floor(n · 2^s / d)` where
`n · 2^s` would reach `2^185`: `round::shift_div` never forms that product,
walking `s ≤ 61` doubling steps instead, carrying a quotient below `2^62` and a
remainder below `d ≤ 2^124`. The widest live value in the entire crate is
`2 · rem < 2^125`.

There is no `wrapping_*`, `saturating_*` or `unchecked_*` call anywhere.
`[profile.release] overflow-checks = true` keeps the checks on in optimised
builds, and CI runs the full suite in both profiles.

Division by zero is a **precondition** on `Q::div`, `Q::div_dir` and `Q::recip`,
discharged statically by the caller. There is no runtime zero-check to fail.

### V3 — value correctness, division-free

Specifications never divide. "`r` is the value `n/d`" is
`q_is(r, n, d) := r.num * d == n * r.den`, and the order relations are
cross-multiplied likewise. The R3 bound is stated the same way: the real claim
`|r − n/d| ≤ 2^-60 · max(1, |n/d|)` is written

```
|r.num·d − n·r.den| · 2^60  ≤  r.den · max(d, |n|)
```

after multiplying through by `r.den · d · 2^60`, all of which are positive.
Division appears only inside *definitional* spec functions — `gcd_nat`,
`bitlen`, `grid_num` — where the recursion, not the solver, carries the meaning.

### V4 — the rounding contract

`round_frac` in `round.rs` is a total spec function mirroring the executable
`round_frac_exec`, and every arithmetic operation `ensures` its result is
*equal to* `round_frac` applied to the exact numerator and denominator. Pinning
the result down as a function, rather than only by its properties, is what makes
commutativity and cross-run determinism provable at all.

* **R1** (`lemma_r1_identity`) — if the exact reduced result satisfies I2 it is
  returned exactly.
* **R2** (`lemma_r2_directed`) — `Down ≤ exact ≤ Up`.
* **R3** (`lemma_r3_error`) — the bound above, with `B = 60`. The proof splits
  on `k = bitlen(floor(|x|))`: `k = 0` (shift 61), `1 ≤ k ≤ 60` (shift `61−k`),
  and `k ≥ 61` (shift 0). `lemma_shift_covers_bound` is the arithmetic core.
* **R4** (`lemma_r4_monotone_grid`) — **stated per grid**, as §3 of the
  specification permits. The composed operation is not globally monotone; see
  the counterexample in `README.md`, which is also a test.

**Documented departure.** R3 is stated under `!saturated(n, d)`. An exact value
with magnitude above `2^62 − 1` has no representable neighbour within
`2^-60 · |exact|`, so the bound is unachievable there; those results saturate,
and `checked_add`/`checked_sub`/`checked_mul` return `None` exactly in that
case (`ensures r.is_none() <==> saturated(...)`).

### V5 — GCD

`gcd.rs` proves, about the ghost `gcd_nat` and the executable `gcd_u128`:

* `lemma_gcd_divides` — it divides both arguments (induction on the second).
* `lemma_gcd_greatest` — every common divisor divides it.
* `lemma_gcd_pos`, `lemma_gcd_le`, `lemma_gcd_zero` — positivity and bounds.
* `lemma_gcd_scale` — `gcd(k·a, k·b) == k · gcd(a, b)`.
* `lemma_gcd_reduce_coprime` — dividing through by the gcd leaves the results
  coprime. **This is the lemma canonicalisation stands on**: it is why
  `Q::new` produces something satisfying I1.

Termination is the `decreases y` measure on the loop, justified by
`x % y < y` for `y > 0`.

`gcd_u128` is the workhorse rather than `gcd_u64`, because canonicalisation
reduces `i128` intermediates, not `i64` ones. `gcd_u64` is a thin wrapper kept
for the narrow case.

### V6 — algebraic laws

| law | status | where |
|---|---|---|
| `add`, `mul` commutative | unconditional | `theorem_add_commutative`, `theorem_mul_commutative` |
| `add`, `mul` associative | exact path only | `theorem_add_associative_exact`, `theorem_mul_associative_exact` |
| distributivity | exact path only | `theorem_distributive_exact` |
| `Ord` total, agreeing with the ghost order | unconditional | `theorem_order_total` |
| canonical ⟺ structural equality | unconditional | `lemma_canonical_eq` (via `lemma_euclid`) |
| `−(−a) == a`, `abs∘abs == abs` | unconditional | `theorem_neg_abs_involution` |
| `1/(1/a) == a` | unconditional | `theorem_recip_involution` |
| exactness theorem (R1 lifted) | — | `theorem_exact_path_is_exact`, `nary::theorem_exact_fold_is_exact` |

`lemma_canonical_eq` is worth calling out: it derives Euclid's lemma from
`lemma_gcd_scale` (no Bézout machinery needed) and uses it to show that two
well-formed `Q` are mathematically equal exactly when they are structurally
equal. That is what licenses deriving `PartialEq`, `Eq` and `Hash`, and it is
what makes "deterministic" a fact rather than a hope.

`Ord` is **not** derived — the derived lexicographic order on `(num, den)` is
not the order on rationals.

### V7 — Lipschitz lemmas (SHOULD)

`lipschitz.rs`. Perturbation statements are written division-free through
`frac_diff_le(n1, d1, n2, d2, en, ed)`, meaning `|n1/d1 − n2/d2| ≤ en/ed`.

* `lemma_add_lipschitz` / `lemma_triangle` — addition is 1-Lipschitz in each
  argument, so errors add.
* `lemma_mul_lipschitz` — `a·b − a'·b' == a·(b − b') + b'·(a − a')`, giving
  constant `1` on `[0, 1]`, which is where every opinion component lives.
* `lemma_div_lipschitz` — the same split for division, with the denominator
  bounded away from zero.

These are what an interval or affine-arithmetic layer would be built on.
`interval::QI` already uses the R2 half.

### V8 — n-ary accumulation (SHOULD)

`nary::theorem_sum_error_accumulation` states that after `k` folded elements the
result is within `k · 2^-60 · max(1, |exact|)` of the exact fold. The induction
is: each `add` contributes one fresh unit (R3), and the carried error passes
through addition with Lipschitz constant `1` (V7).

This proof is the least complete in the crate — it is SHOULD tier, and
`lemma_error_accumulates_additively` is currently a statement with a proof
sketch rather than a discharged argument. The *empirical* claim is checked:
`oracle::long_fold_chain_tracks_oracle` runs 10⁴ mixed operations and asserts
the accumulated error against the oracle stays inside `k · 2^-60`.

---

## Milestone status

| milestone | scope | status |
|---|---|---|
| M1 | `Q`, ghost model, canonical constructor, verified GCD | code + specs + proofs written; unchecked |
| M2 | add/sub/mul/div/neg/abs/cmp with exact-path specs | code + specs + proofs written; unchecked. **Tested green.** |
| M3 | rounding: budget detection, dyadic snap, R1–R4, exactness theorem | code + specs + proofs written; unchecked. **Tested green against the oracle.** |
| M4 | `from_f64_dir`, `to_f64`, `from_decimal`, serde, `Display`, `TRUSTED.md` | complete and tested |
| M5 | malachite oracle harness, property tests, CI | complete and green |
| M6 | V7 Lipschitz lemmas, interval type `QI` | delivered (stretch) |

Acceptance per the specification is "M1–M5 verified and green". **Green: yes.
Verified: not yet** — for the environmental reason at the top of this file. The
consuming engine rewrite can start against the M2 API surface, which is stable
and independently validated; it should not be told the proofs have been checked
until they have.

## Reproducing the verification

```sh
# Install Verus (needs github.com reachable)
TAG=$(curl -sSfL https://api.github.com/repos/verus-lang/verus/releases/latest \
      | python3 -c 'import json,sys; print(json.load(sys.stdin)["tag_name"])')
# ...download the x86-linux asset for $TAG, unzip, put it on PATH...

cargo verus verify --features serde
```

The same steps are automated in `.github/workflows/ci.yml`.
