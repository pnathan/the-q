# Verification status

## Read this first

**`cargo verus verify` discharges every proof obligation in this crate.**

```
verification results:: 2058 verified, 0 errors     <- vstd
verification results::  691 verified, 0 errors     <- the-q
```

That second line is the number that matters, and it is the one to quote. Do not
count `error:` lines in the log: Verus prints callee context lines that also
start with `error`, so grepping inflates the total by roughly half. (I did
exactly that for several rounds and reported numbers 60–80% too high. The
authoritative figure is the `verification results` line.)

The `verus verify` job is a **required** CI check.

The trajectory, one row per CI round:

| head | verified | errors |
|---|---|---|
| `67661e1` | 255 | 36 |
| `ab17e4d` | 288 | 53 |
| `8b689af` | 305 | 46 |
| `864e499` | 317 | 45 |
| `686bcc9` | 329 | 42 |
| `ddaac00` | 355 | 22 |
| `6a82bb1` | 357 | 24 |
| `048899e` | 373 | 20 |
| `fcc13c5` | 389 | 13 |
| `6a5890f` | 404 | 9 |
| `a0da72b` | 423 | 7 |
| `c87f563` | 431 | 3 |
| `e267cd5` | 440 | 1 |
| `c1e3e54` | 442 | 0 |
| `6c73847` (`main`) | 443 | 0 |
| `5edea2e` (five merged lines of work) | 665 | 0 |
| this branch (ingestion contracts, #9) | **691** | **0** |

Verified conditions rose monotonically. The error count did not, and both
directions had honest causes: it rose when a fixed well-formedness failure
unblocked checking of proofs that were previously never reached, when new
obligations were added (restating V7/V8 added ~25 `requires`/`ensures`), and
when a strengthened precondition handed its callers a new obligation
(`6a82bb1`, where `magnitude_fits_exec` acquired the input bound its `0 - n`
actually needed); it fell when proofs landed.

The jump at `ddaac00` is the one worth understanding. `lemma_pow2_124`,
`lemma_pow2_125` and `lemma_pow2_126` were stated by `reveal_with_fuel`, and
past roughly `2^64` that stops working — the unfolding is linear in the exponent
and Z3 exhausts its resource limit before reaching the literal. Every `i128`
overflow check in the crate is discharged from one of those literals, so three
unproven lemmas were starving the whole rounding path. Deriving them by squaring
`2^62` closed twenty errors at once. **A failing lemma still hands its `ensures`
to its callers**, which is why the damage was invisible in the call graph for
several rounds.

## How this crate came to be written without a verifier

The Verus verifier is a binary distributed through GitHub releases, and the
environment this crate was authored in returns `403` for `github.com`. The
libraries (`vstd`, `verus_builtin`, `verus_builtin_macros`) are on crates.io and
do compile, which is why `cargo build` works and the crate is usable. CI, which
does have egress, installs the verifier and runs it.

The practical consequence, and the thing to keep in mind reading the proof
bodies: **`cargo build` passing means the executable code is well-typed and says
nothing whatsoever about the specifications.** Ghost code is erased by rustc, so
type errors in specs, missing triggers, and datatype-opaqueness violations are
all invisible locally and only surface in CI. Every proof change here costs a
~12-minute round trip.

## What is established independently of the proofs

* 57 tests green in debug and release, on every commit.
* Differential tests against `malachite-q` — arbitrary precision, fully
  independent: 20,000 random cases per operation per rounding direction against
  R1, R2 and R3, plus exhaustive coverage of every `p/q` with `|p| <= 12,
  q <= 12` (90,000 pairs x 4 operations x 3 directions).
* Overflow checks on in both profiles, so the V2 no-overflow claim has been
  executed against roughly ten million operations without a panic.
* Determinism checked byte-for-byte across eight concurrent threads.

This is strong evidence, and it is not what §6 and §8 ask for — those want the
proofs machine-checked. Both now hold: §8's acceptance criterion is "M1–M5
verified and green", and the crate is green *and* verified.

## What to know before touching the proofs

Most of the work went into `round.rs` — the dyadic-snap rounding contract, which
§3 calls "the heart of the design". Six classes of problem accounted for nearly
all of it, and each is worth knowing:

1. **Bounds stated with `pow2(n)` prove nothing about an `i128`.** `pow2` is an
   opaque recursive spec function. Every arithmetic operation in `q.rs` was
   failing its overflow check until `lemma_op_widths` was restated with literal
   bounds alongside the `pow2` ones.
2. **`by (nonlinear_arith)` blocks are context-isolated.** They see only what
   their own `requires` lists — *not* the surrounding proof context. Steps that
   combine earlier facts must be plain `assert`s.
3. **Partially-factored ring identities exhaust the resource limit,** because
   the solver has to rediscover the factorisation. Splitting distribution from
   rearrangement leaves goals that are pure associativity/commutativity
   shuffles, which Z3 normalises for free. This alone took `interval.rs` to
   zero.
4. **Outside a `nonlinear_arith` block, multiplication is uninterpreted.** So
   `qf * rd` and `rd * qf` are simply different terms, and a plain `assert` that
   needs them identified will fail without any hint that commutativity was the
   problem. `lemma_fundamental_div_mod_converse` wants the divisor first, which
   is the far end of the crate's own reduction equations; three call sites
   needed an explicit `assert(a * b == b * a) by (nonlinear_arith)` to bridge.
   This goes further than it sounds: even `0 * g` is uninterpreted, so deriving
   `n == 0` from `n == 0 * g` is a nonlinear step.
5. **A recursive spec function's default fuel is 1.** `pow2(1)` unfolds once, to
   `2 · pow2(0)`, and stops — so `assert(pow2(1) == 2)` fails. Conversely
   `reveal_with_fuel(pow2, 125)` is not a proof either; it is an rlimit
   exhaustion waiting to happen. Both ends of the range need pinned lemmas.
6. **A failing lemma still hands its `ensures` to its callers.** This makes a
   broken foundation invisible in the call graph: `lemma_op_widths` verified
   cleanly for rounds while the `pow2` literals it rests on did not. Read the
   whole error list, not just the errors in the module you are working on.

A practical corollary of (6): when a conjunctive postcondition like `wf()` fails,
the solver names only the conjunction. Asserting each clause separately turns one
opaque failure into a pointer at the clause that is actually missing — that is
how the last four errors in `round.rs` were found, and the asserts were worth
keeping.

## One thing verification found that testing could not

`lemma_snap_in_budget` was stated with a hypothesis missing, and the stated
bound was **false without it**. At the clamped shift (`k >= 62`, `s == 0`) the
snap returns `ceil(|x|)`, so the budget bound needs `floor(|x|) < MAX_MAG`
strictly; nothing ruled out equality. If it were equal then
`|rn| == MAX_MAG * rd` exactly, so `rd` divides `|rn|`. Coprimality of the
reduced pair rules that out — it forces `rd == 1`, whence `|rn| == MAX_MAG`,
which means the pair *did* fit the budget, contradicting the hypothesis that it
did not.

The differential suite could never have caught this: it only ever exercises
reduced pairs, so the missing hypothesis always happened to hold. That is the
case for doing this at all.

## The CI check

`verus verify` is a required job. It was `continue-on-error: true` while the
proofs were being discharged — an advisory red is more honest than a hidden
failure — and was flipped once the count reached zero. A regression in any proof
now fails the build.

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
| V8 | N-ary accumulation bound `k · 2^-B` | SHOULD | `nary::theorem_sum_error_accumulation`, `nary::theorem_product_error_accumulation`, `nary::theorem_wm_num_error_accumulation`, `nary::theorem_wm_denom_error_accumulation` |

### V1 — the type invariant

`Q::wf(self)` in `model.rs` is the conjunction of I1 and I2:

```
den > 0  ∧  gcd(|num|, den) == 1  ∧  (num == 0 ⟹ den == 1)
         ∧  |num| ≤ 2^62 − 1      ∧  den ≤ 2^62 − 1
```

Every constructor `ensures` it, every operation `requires` it of its inputs and
`ensures` it of its result. The `Q` fields are public — Verus cannot state a
public invariant about a datatype whose fields it cannot see — so a caller *can*
write `Q { num: 3, den: 0 }`; what it cannot do is pass it to anything, since
every operation requires the invariant and a malformed value cannot discharge
it. `serde` deserialisation goes through `Q::new` and returns an error rather
than a malformed value.

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
`|r − n/d| ≤ 2^-61 · max(1, |n/d|)` is written

```
|r.num·d − n·r.den| · 2^61  ≤  r.den · max(d, |n|)
```

after multiplying through by `r.den · d · 2^61`, all of which are positive.
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
* **R3** (`lemma_r3_error`) — the bound above, with `B = 61`. The proof splits
  on `k = bitlen(floor(|x|))`: `k = 0` (shift capped at 61), `1 ≤ k ≤ 61`
  (shift `62−k`), and `k ≥ 62` (shift 0). `lemma_shift_covers_bound` is the
  arithmetic core.
  **`Dir::Nearest` additionally achieves `B = 62`** (`lemma_r3_error_nearest`,
  `within_error_bound_nearest`): a round-to-nearest pick is never more than
  half a grid step away, proved by the half-step form of the grid-error lemma
  (`lemma_grid_error_step_nearest_half`, division-free
  `2·|sn·rd − rn·2^s| ≤ rd`) composed the same way R3 itself is. This is
  additional to the uniform `B = 61` statement, not a replacement for it — the
  directed modes stay at `61` — and `Q::add`/`sub`/`mul`/`div` (the only
  operations that fix `dir = Nearest`) `ensures` both.
* **R4** (`lemma_r4_monotone_grid`) — **stated per grid**, as §3 of the
  specification permits. The composed operation is not globally monotone; see
  the counterexample in `README.md`, which is also a test.

**Documented departure.** R3 is stated under `!saturated(n, d)`. This scopes the
contract below the magnitude ceiling by *choice*: it is tempting to say the
bound is unachievable above it, but that is false — `MAX_MAG + 1/2` sits within
`2^-61` of `MAX_MAG/1`. Keeping the contract on one clean side of the boundary
is the reason. Those results saturate,
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
* `lemma_mul_lipschitz` — the algebraic identity
  `a·b − a'·b' == a·(b − b') + b'·(a − a')`.
* `lemma_div_lipschitz` — the same split for division.

Those two are *identities*, not bounds, and an identity will not compose two
`frac_diff_le` hypotheses through a product or a quotient. The bounds that will
are stated alongside them, with the identities left untouched for the callers
that use them directly:

* `lemma_mul_lipschitz_bound` — `|a·b − a'·b'| ≤ (ca·e₂ + cb·e₁)/ed` given
  `|a| ≤ ca` and `|b'| ≤ cb`. `lemma_mul_lipschitz_unit` is the `ca = cb = 1`
  corollary: on `[0, 1]`, where every opinion component lives, the errors
  simply add.
* `lemma_recip_lipschitz_bound` — `|1/b − 1/b'| ≤ (e₂·md²)/(ed·mn²)` for
  `b, b' ≥ mn/md > 0`. The lower bound is supplied division-free as
  `mn·bd ≤ md·bn`; a caller with `b ≥ 1/2` passes `mn = 1, md = 2`. The `md²`
  is the genuine quadratic cost of perturbing a divisor.
* `lemma_div_lipschitz_bound` — the quotient bound, proved as the reciprocal
  bound fed into the product bound rather than by attacking the four-way
  cross-multiplied difference directly. That composition is both shorter and
  far cheaper for the solver.

Supporting these: `lemma_abs_triangle`, `lemma_abs_prod` (`|u·v| == |u|·|v|`
with *both* signs unknown, which `model::lemma_abs_mul_pos` does not cover),
`lemma_frac_diff_scale`, and scalar and pairwise product monotonicity.

These are what an interval or affine-arithmetic layer would be built on.
`interval::QI` already uses the R2 half.

### V8 — n-ary accumulation (SHOULD)

`nary::theorem_sum_error_accumulation` states that after `k` folded elements the
result is within `k · m · 2^-61` of the exact fold, where `m` bounds the
intermediates. The induction is: each `add` contributes one fresh unit (R3), and
the carried error passes through addition with Lipschitz constant `1` (V7); both
halves are `lipschitz::lemma_abs_error_step`.

**This is stated as an absolute bound, not a relative one, and that is a
correction rather than a weakening.** The specification's phrasing suggests
`k · 2^-61 · max(1, |exact|)`, but relative error does not accumulate by
induction: the magnitude in the bound is the magnitude of the *running* sum,
which moves at every step, so the induction hypothesis and the goal are about
different quantities. Carrying an explicit magnitude bound `m` on the
intermediates is what makes the statement provable and, for the consuming
engine — where every value lies in `[0, 1]` and `m == 1` — it says the same
thing.

The empirical claim is checked independently:
`oracle::long_fold_chain_tracks_oracle` runs 10⁴ mixed operations and asserts
the accumulated error against the oracle stays inside `k · 2^-61`.

**`product` and `weighted_mean` carry the same shape of bound, each under its
own hypothesis, not `sum`'s hypothesis reused.**

* `nary::theorem_product_error_accumulation` is `sum`'s theorem's
  multiplicative twin: `k · m · 2^-61`, but only under `nary::all_unit(s)` —
  every factor's magnitude at most `1`. This is necessary, not a proof
  artifact: multiplication is 1-Lipschitz only when weighted by the other
  operand's magnitude (`lipschitz::lemma_mul_lipschitz`), so a factor `> 1`
  would amplify the carried error geometrically rather than additively, and
  no bound of this shape would hold uniformly in `k`. The hypothesis is
  trivial in the consuming engine's domain (`[0, 1]`).
* `weighted_mean` gets two bounds on its two internal accumulators —
  `nary::theorem_wm_num_error_accumulation` (`2k · m · 2^-61` against the true
  `Σ w_i·x_i`, twice `sum`'s rate because each pair costs two roundings) and
  `nary::theorem_wm_denom_error_accumulation` (`k · m · 2^-61` against the
  true `Σ w_i`, a direct restatement of `theorem_sum_error_accumulation` for
  the weight half of each pair) — but **not** a single bound on the value
  `weighted_mean` returns. Composing the two through the final division would
  need the exact weight sum bounded away from zero as a further explicit
  hypothesis. The other thing it needed — a usable division error bound — now
  exists (`lipschitz::lemma_div_lipschitz_bound`); when this text was first
  written only the algebraic identity did. So the composition is unblocked but
  still unproven, and the two theorems above remain the actual n-ary-helper
  internals V8 asks be bounded.

---

## Milestone status

| milestone | scope | status |
|---|---|---|
| M1 | `Q`, ghost model, canonical constructor, verified GCD | verified and tested |
| M2 | add/sub/mul/div/neg/abs/cmp with exact-path specs | verified and tested |
| M3 | rounding: budget detection, dyadic snap, R1–R4, exactness theorem | verified and tested against the oracle |
| M4 | `from_f64_dir`, `to_f64`, `from_decimal`, serde, `Display`, `TRUSTED.md` | complete and tested |
| M5 | malachite oracle harness, property tests, CI | complete and green |
| M6 | V7 Lipschitz lemmas, interval type `QI` | delivered (stretch), verified |

Acceptance per the specification is "M1–M5 verified and green". **Both hold.**
The consuming engine rewrite can start against the M2 API surface.

## Reproducing the verification

```sh
# Install Verus (needs github.com reachable)
TAG=$(curl -sSfL https://api.github.com/repos/verus-lang/verus/releases/latest \
      | python3 -c 'import json,sys; print(json.load(sys.stdin)["tag_name"])')
# ...download the x86-linux asset for $TAG, unzip, put it on PATH...

cargo verus verify --features serde
```

The same steps are automated in `.github/workflows/ci.yml`.
