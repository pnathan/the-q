# Verification status

```
verification results:: 2058 verified, 0 errors     <- vstd
verification results:: 1093 verified, 0 errors     <- the-q
```

The second line is the figure to quote; take it from the `verification
results` line, not from a count of `error:` lines, which Verus also prints for
callee context. `verus verify` is a required CI check. No `assume(...)` or
`admit()` appears in `src/`. Three functions are `external_body`, all in
`TRUSTED.md`: `from_f64_dir` and `to_f64` at the `f64` edge, and
`q::require_condition`, a runtime guard trusted for its panic message only.

`convert::pow10_i128`, `convert::from_decimal128_dir`, and
`convert::from_decimal128_exact` (issue #33, the `mantissa · 10^-scale`
boundary a `rust_decimal::Decimal` needs, and the refuse-rather-than-round
path into `Exact`) account for the five added since the count above was last
quoted.

## Independent of the proofs

* 207 default-feature and 217 all-feature tests, debug and release, plus six
  doctests, four of them `compile_fail` checks that `Rat` and `QI` cannot be
  built or mutated from outside the crate.
* Differential tests against `malachite-q`: 20,000 random cases per operation
  per direction against R1–R3, plus every `p/q` with `|p|, q ≤ 12`.
* Overflow checks on in both profiles; byte-identical results across eight
  threads.
* Transcendental accuracy measured against two independent oracles (see
  `README.md`); it is not proven.

## Obligation map

| # | Obligation | Where |
|---|---|---|
| V1 | invariant preserved by every public operation | `Rat::wf` in `model.rs`; `requires`/`ensures` on every public function |
| V2 | no panic, no overflow | `q::lemma_op_widths`, `round::lemma_quotient_bound`, `round::shift_div`, `model::lemma_mul_in_i128` |
| V3 | value correctness against the ghost model, division-free | `model::q_is`/`q_eq`/`q_le`; `round::lemma_r1_identity` |
| V4 | rounding contract R1–R4 | `round::lemma_r1_identity`, `lemma_r2_directed`, `lemma_r3_error`, `lemma_r3_error_nearest`, `lemma_r4_monotone_grid` |
| V5 | GCD correctness and termination | `gcd.rs` |
| V6 | algebraic laws | `laws.rs` |
| V7 | Lipschitz bounds | `lipschitz.rs` |
| V8 | accumulation bounds | `nary::theorem_sum_error_accumulation`, `theorem_product_error_accumulation`, `theorem_wm_num_error_accumulation`, `theorem_wm_denom_error_accumulation`, `theorem_weighted_mean_return_error` |
| V9 | `Q`: totality, classification, order | `ext.rs` |
| V10 | transcendentals: totality, termination | `transcendental.rs` |

### V1 — the invariant

`Rat::wf`: `den > 0 ∧ gcd(|num|, den) == 1 ∧ (num == 0 ⟹ den == 1) ∧ |num| ≤
2^62 − 1 ∧ den ≤ 2^62 − 1`. Every constructor ensures it; every operation
requires it of inputs and ensures it of outputs. The fields are private; public
contracts use the closed accessors `n()` and `d()`. Serde deserialisation goes
through `Rat::new` and errors rather than producing a malformed value. At
runtime, `common::assert_wf` re-derives canonicality with an independent gcd on
every value the property and oracle suites produce.

### V2 — no panic, no overflow

Every `i128` intermediate is bounded: products of two in-budget values are
below `2^124`, sums of two such products below `2^125`. The rounding step needs
`floor(n · 2^s / d)` where `n · 2^s` would reach `2^185`; `round::shift_div`
never forms it, walking `s ≤ 61` doubling steps with a quotient below `2^62`
and a remainder below `d`. No `wrapping_*`, `saturating_*` or `unchecked_*`
appears anywhere; `overflow-checks = true` in release.

Division by zero is a precondition on `Rat::div`, `Rat::div_dir` and
`Rat::recip`. Verified callers discharge it statically; for unverified callers
`q::require_condition` turns it into a panic with a message naming the
operation. `QI::new` guards `lo ≤ hi` the same way.

### V3 — division-free specification

"`r` is `n/d`" is `r.num · d == n · r.den`; order and error bounds are
cross-multiplied likewise. R3, `|r − n/d| ≤ 2^-61 · max(1, |n/d|)`, is stated
as `|r.num·d − n·r.den| · 2^61 ≤ r.den · max(d, |n|)`. Division appears only
inside definitional spec functions (`gcd_nat`, `bitlen`, `grid_num`).

### V4 — the rounding contract

`round_frac` is a total spec function mirroring `round_frac_exec`, and every
operation ensures its result *equals* `round_frac` of the exact pair. Pinning
the function, not just its properties, is what makes commutativity and
determinism provable.

* R1 `lemma_r1_identity`; R2 `lemma_r2_directed`.
* R3 `lemma_r3_error`, `B = 61`, split on `k = bitlen(floor(|x|))`: `k = 0`
  (shift capped at 61), `1 ≤ k ≤ 61`, `k ≥ 62` (shift 0). `Dir::Nearest`
  additionally achieves `B = 62` (`lemma_r3_error_nearest`), and
  `add`/`sub`/`mul`/`div` ensure both.
* R4 `lemma_r4_monotone_grid`, per grid. The composed operation is not
  globally monotone; `README.md` has the counterexample, which is also a test.
* R3 is scoped by `!saturated(n, d)`; above the ceiling results saturate and the
  four `checked_*` operations return `None` exactly there.

`lemma_snap_in_budget` is the one place verification found a false statement
that tests could not have: at the clamped shift the snap returns `ceil(|x|)`,
and the budget bound needs `floor(|x|) < MAX_MAG` *strictly*. Equality is ruled
out by coprimality of the reduced pair. The differential suite only ever sees
reduced pairs, so the missing hypothesis always happened to hold.

### V5 — GCD

`lemma_gcd_divides`, `lemma_gcd_greatest`, `lemma_gcd_pos`/`le`/`zero`,
`lemma_gcd_scale`, and `lemma_gcd_reduce_coprime`, which is what canonicalisation
stands on. Termination by `decreases y`. The workhorse is `gcd_u128` (Stein's
binary algorithm narrowed to `u64`), because canonicalisation reduces `i128`
intermediates.

### V6 — laws

| law | scope | where |
|---|---|---|
| `add`, `mul` commutative | unconditional | `theorem_add_commutative`, `theorem_mul_commutative` |
| associativity, distributivity | exact path | `theorem_add_associative_exact`, `theorem_mul_associative_exact`, `theorem_distributive_exact` |
| associativity defect bounded | `4·2^-61·m` (add); `6·2^-61` on `[0,1]` (mul) | `theorem_add_associativity_bound`, `theorem_mul_associativity_bound_unit_interval` |
| `Ord` total, agreeing with the value order | unconditional | `theorem_order_total` |
| canonical ⟺ structural equality | unconditional | `lemma_canonical_eq` |
| `−(−a) == a`, `abs ∘ abs == abs`, `1/(1/a) == a` | unconditional | `theorem_neg_abs_involution`, `theorem_recip_involution` |
| a fold that never rounds is exact | — | `theorem_exact_path_is_exact`, `nary::theorem_exact_fold_is_exact` |

`Ord` is not derived: the lexicographic order on `(num, den)` is not the order
on rationals.

### V7 — Lipschitz

Stated division-free through `frac_diff_le(n1, d1, n2, d2, en, ed)`, meaning
`|n1/d1 − n2/d2| ≤ en/ed`. `lemma_add_lipschitz` (errors add);
`lemma_mul_lipschitz_bound`, `|a·b − a'·b'| ≤ ca·e₂ + cb·e₁` given `|a| ≤ ca`,
`|b'| ≤ cb`; `lemma_recip_lipschitz_bound`, `|1/b − 1/b'| ≤ e₂·md²/(ed·mn²)`
for `b, b' ≥ mn/md > 0`; `lemma_div_lipschitz_bound`, the composition.

### V8 — accumulation

`theorem_sum_error_accumulation`: after `k` folded elements the result is within
`k · m · 2^-61` of the exact fold, `m` bounding the intermediates. The bound is
absolute, not relative: relative error does not accumulate by induction because
the magnitude in the bound moves at every step. `theorem_product_error_accumulation`
is the same shape under `all_unit` (every factor's magnitude at most 1),
without which a factor above 1 amplifies carried error geometrically.
`weighted_mean` has bounds on both accumulators (`2k·m·2^-61` on the numerator,
`k·m·2^-61` on the weights) and `theorem_weighted_mean_return_error` composes
them through the division: with weights and values in `[0, 1]` and the exact
weight sum at least `δ = delta_num/delta_den`, the returned value is within
`8k · delta_den / (delta_num · 2^61)` of the exact mean.
`oracle::long_fold_chain_tracks_oracle` checks the sum bound over 10⁴ operations.

### V9 — `Q`

Every operation is total; `theorem_classification_partitions`,
`theorem_order_total`, `theorem_order_antisymmetric` (against structural
equality), `theorem_order_transitive`, `theorem_spec_eq_is_structural_eq`,
`theorem_sat_separates_numbers`; `Nan` absorbs in `add`/`sub`/`mul`/`div`. The
propagation tables are deliberately *not* restated as ghost functions (a spec
shaped like the table it specifies verifies with a shared mistake); they are
pinned by exhaustive enumeration of the 6×6 state space in
`tests/extended_q.rs`. The order is on representations: `PosSat == PosSat` even
though the two true values may differ.

### V10 — transcendentals

Every function returns a well-formed `Q` for every input; every loop has a
fixed constant bound and `decreases`; `isqrt_i64` satisfies
`r² ≤ n < (r+1)²`. Accuracy is not proven. Each series length is derived from
its tail bound against the `2^-61` grid and recorded beside the constant.

## Verus notes

1. Bounds stated with `pow2(n)` discharge nothing about an `i128`; state the
   literal alongside (`lemma_pow2_124/125/126`, derived by squaring, since
   `reveal_with_fuel` exhausts the resource limit past `2^64`).
2. `by (nonlinear_arith)` sees only its own `requires`, not the surrounding
   context.
3. Split distribution from rearrangement; partially factored ring identities
   exhaust the solver.
4. Outside a nonlinear block multiplication is uninterpreted, so `a * b` and
   `b * a` are different terms; even `0 * g` needs a nonlinear step.
5. A recursive spec function's default fuel is 1.
6. A failing lemma still hands its `ensures` to its callers. Read the whole
   error list.

## Reproducing

```sh
VERUS_VERSION=0.2026.07.27.31579f0
curl -sSfL "https://github.com/verus-lang/verus/releases/download/release/${VERUS_VERSION}/verus-${VERUS_VERSION}-x86-linux.zip" -o /tmp/verus.zip
# unzip; put the cargo-verus directory on PATH
cargo verus verify --locked --all-features -- --multiple-errors 8
```

`.github/workflows/ci.yml` runs the same command.
