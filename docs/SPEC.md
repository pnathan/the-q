# Verified Rational (ℚ) Arithmetic Core — Specification

> This is the specification this crate was built from, reproduced verbatim as
> the record of intent. Where the implementation departs from it — and there are
> three places — the departures are called out in `README.md` ("Honesty notes")
> and `VERIFICATION.md`, not silently absorbed here.
>
> The three departures, in brief:
>
> 1. **Magnitude saturation.** R3 is stated unconditionally below, but it cannot
>    hold for an exact value whose magnitude exceeds `2^62 − 1`; those results
>    saturate and the `checked_*` variants report them.
> 2. **`Q::new`.** §2.1 claims every `i64` pair fits I2 after reduction.
>    `Q::new(i64::MAX, 1)` does not, so `new` returns `None` there too;
>    `new_rounded` is the total variant.
> 3. **GCD width.** V5 says "u64 Euclid"; canonicalisation reduces `i128`
>    intermediates, so the verified workhorse is `gcd_u128` with `gcd_u64` as a
>    wrapper.

**Purpose.** A standalone Rust crate providing exact-with-verified-rounding
rational arithmetic, checked by **Verus**, to serve as the numeric backbone of a
subjective-logic fusion engine (a ℚ rewrite of `uncertain-logic`). This document
is **self-contained**: it is the complete brief for a fresh repo built by a cold
session with no access to the parent monorepo.

**Why this exists (context in four sentences).** The fusion engine's mathematics
(Jøsang cumulative/averaging belief fusion, opinion algebra) is rational-closed;
its current `f64` implementation is non-deterministic across evaluation orders,
non-associative, and unverifiable. External bignum crates are unusable: the best
one (malachite-q) is LGPL-3.0-only (blocker for statically linked proprietary
binaries), and under Verus *any* external crate's arithmetic enters the proof as
unverified axioms — there is **no verified bignum or rational anywhere in the
Verus ecosystem** (confirmed 2026-07; this crate is first-of-kind). The chosen
design is a **bounded rational with verified directed rounding**: exact
arithmetic while values fit a fixed width budget, machine-checked error bounds
when they don't. Full verified arbitrary precision (`Vec<u64>` limbs) is
explicitly OUT OF SCOPE — it is the escalation path only if benchmarks show
rounding bites (it is an order-of-magnitude larger verification project).

**Naming.** Do NOT name anything `uncertain-logic-2`/`-v2` (collides with an
existing unrelated crate in the parent monorepo). Crate name is the repo owner's
choice; this spec calls the type `Q`.

---

## 1. Representation and invariants

```rust
pub struct Q { num: i64, den: i64 }   // value = num / den
```

Type invariants — **every public function requires them on inputs and ensures
them on outputs** (Verus obligation V1):

- **I1 (canonical):** `den > 0` and `gcd(|num|, den) == 1` (and `num == 0 ⟹ den == 1`).
- **I2 (bounded):** `|num| ≤ 2^62 − 1` and `den ≤ 2^62 − 1`.

Canonical form gives: structural equality ⟺ mathematical equality (so `Eq`,
`Ord`, `Hash` are all derivable-safe), and deterministic bit-exact
representation of every value.

**Why the bound is 2^62, not 2^63 — the overflow arithmetic (V2).** All
intermediate computation is done exactly in `i128`:

| Op | Worst intermediate | Bound under I2 | i128-safe? |
|---|---|---|---|
| mul | `num₁·num₂`, `den₁·den₂` | ≤ (2^62−1)² < 2^124 | yes |
| add/sub | `num₁·den₂ ± num₂·den₁` | ≤ 2·(2^62−1)² < 2^125 | yes |
| add/sub | `den₁·den₂` | < 2^124 | yes |
| cmp | `num₁·den₂` vs `num₂·den₁` | < 2^124 | yes |

With a 2^63 budget the add-numerator hits 2^127, which overflows `i128::MAX =
2^127 − 1`. The 2^62 budget leaves headroom; every intermediate is provably in
range and **no arithmetic panic or overflow is possible** (Verus checks this
mechanically — that is obligation V2, and it must hold with overflow checks ON,
no `wrapping_*`).

**Ghost model.** Specifications are stated against a mathematical model in
Verus's unbounded `int` ghost types. Do NOT use SMT division in specs — state
all value correctness **division-free by cross-multiplication**, e.g. the spec
"r = a + b" is `r.num * (a.den * b.den) == (a.num * b.den + b.num * a.den) * r.den`
over ghost `int`. (This mirrors the Lean formalization discipline of the parent
research program and avoids the worst SMT instability.) A `spec fn` pair
`(q.num as int, q.den as int)` plus relational predicates
`q_eq(a, b) := a.num * b.den == b.num * a.den`, `q_le`, etc., is the model
everything is proven against.

---

## 2. Operation inventory

Derived from a full scan of the consuming engine (`uncertain-logic`); this is
the complete surface the fusion rewrite needs. The engine's own formulas (CBF:
`(b₁u₂ + b₂u₁)/(u₁ + u₂ − u₁u₂)` etc.) live in the ENGINE crate, composed from
these primitives — do not build fusion into the Q crate.

### 2.1 MUST — constructors

| Function | Contract |
|---|---|
| `Q::zero()`, `Q::one()` | exact constants |
| `Q::from_int(i: i64)` | exact for `|i| ≤ 2^62 − 1`; error/None otherwise |
| `Q::new(num: i64, den: i64) -> Option<Q>` | None iff `den == 0`; otherwise canonicalize (sign to den>0, GCD-reduce). Inputs within i64 always fit I2 after reduction — exact, never rounds |
| `Q::from_decimal(mantissa: i64, dec_places: u8) -> Option<Q>` | exact decimal input, e.g. `(85, 2) = 0.85` — the engine's reliability/competence/weight inputs are short decimals; this is the primary ingestion path |
| `Q::from_f64_dir(v: f64, dir: Dir) -> Option<Q>` | `Dir ∈ {Down, Up, Nearest}`. None on NaN/±inf. Result is a representable Q with the directed inequality vs the exact real value of `v`, and `|result − v| ≤ 2^-B·max(1, |v|)` (B per §3). Restriction to `|v| ≤ 2^61` is acceptable. See §5 boundary note |

### 2.2 MUST — arithmetic

Each returns a canonical, bounded, possibly-rounded result; see §3 for the
rounding contract.

| Function | Notes |
|---|---|
| `add(a, b)`, `sub(a, b)` | exact in i128, reduce, round-to-budget |
| `mul(a, b)` | same |
| `div(a, b)` | `requires !b.is_zero()` — division by zero is a **precondition**, statically discharged by the caller (Verus), never a runtime panic path |
| `neg(a)`, `abs(a)` | always exact (I2 symmetric in sign) |
| `recip(a)` | `requires !a.is_zero()`; always exact (swaps num/den) |
| `min(a, b)`, `max(a, b)`, `clamp(a, lo, hi)` | exact; `clamp requires lo ≤ hi` |

### 2.3 MUST — comparison and predicates (all EXACT, no epsilon, total)

`eq`, `lt`, `le`, `cmp` (implement `Ord` — ℚ has a total order, an upgrade over
`f64`'s `PartialOrd`); `is_zero`, `is_one`, `signum`, `in_unit_interval`
(`0 ≤ q ≤ 1` — the engine checks this constantly on beliefs/disbeliefs/
uncertainties). Comparison via i128 cross-multiplication, proven correct
against the ghost order.

### 2.4 MUST — conversions out and plumbing

| Item | Contract |
|---|---|
| `to_f64(q)` | for display/DTO boundary ONLY. This is the one **documented trusted boundary** (`external_body`): proving float rounding in Verus is not worth it. Covered by differential tests instead (§6). Never fed back into Q arithmetic |
| `Display` | `"num/den"` |
| `serde` (feature-gated) | serialize as the `(num, den)` integer pair — **exact round-trip**, unlike any f64 encoding |
| `Hash`, `Eq`, `Ord`, `Clone`, `Copy` | derive; safe because canonical. `Copy` matters: plain 128-bit value type, no heap, trivially `Send + Sync` (the engine holds opinions inside `RwLock`/`Mutex` shared state) |

### 2.5 SHOULD — n-ary helpers (the ABF formula shape)

`sum(&[Q])`, `product(&[Q])`, `weighted_mean(&[(Q, Q)])` — defined as binary
folds (left-to-right, fixed order) so V2 safety is inherited; ensures-clause
gives the accumulated error bound `k·2^-B` after `k` elements. Do NOT do n-ary
i128 accumulation (re-opens overflow analysis for no benefit).

### 2.6 OUT OF SCOPE

No transcendental functions of any kind — no `exp`, `ln`, `pow` with rational
exponent, `sqrt`. (The consuming engine's four transcendental sites — the
log-space ABF path, which is dead code under exact arithmetic; temporal
half-life decay; numeric-similarity; entropy diagnostics — are handled on the
ENGINE side as f64 pre-passes whose outputs enter through `from_f64_dir`.)
No arbitrary precision. No `int_pow` unless trivially cheap
(`u32` exponent as repeated `mul`, inheriting its bounds).

---

## 3. The rounding contract (the heart of the design)

`round_to_budget(x_exact, dir)` is the internal step applied when an exact i128
intermediate, after GCD reduction, still violates I2. Public contract, per
arithmetic op (obligation V4):

- **R1 (identity on representables):** if the exact reduced result satisfies
  I2, the op returns it **exactly**. Consequence, stated as a theorem: any
  computation whose exact values all fit the budget is END-TO-END EXACT. Small
  investigations pay zero rounding.
- **R2 (directed):** `Dir::Down` result ≤ exact value ≤ `Dir::Up` result.
  Default mode for plain ops is `Nearest`; the directed modes exist so a future
  interval layer can bracket without new proofs.
- **R3 (error bound):** `|result − exact| ≤ 2^-B · max(1, |exact|)` with
  **B ≥ 60**. The implementer chooses the algorithm — the two candidates:
  - *Dyadic snap*: round to the grid `k / 2^s` with `s` chosen per magnitude
    (floating-point-like). Easiest Verus proof; error bound is direct.
  - *Stern–Brocot / continued-fraction best approximant* with `den ≤ 2^62 − 1`:
    tighter results, harder proof (loop invariant + termination measure).

  Dyadic snap is the recommended first implementation; R3 with B = 60 is the
  acceptance bar either way.
- **R4 (monotone):** `x ≤ y ⟹ round(x, dir) ≤ round(y, dir)` — needed so the
  engine's clamp/order logic survives rounding. (May be stated per-grid; for
  dyadic snap it is easy.)

**Honesty consequence to document in the crate README:** with rounding,
`add`/`mul` are commutative (prove it — V6) but **not associative in general**;
associativity holds on the exact path (prove that too). The consuming engine's
order-independence claims therefore hold exactly for small cases and up to the
accumulated error bound in general. Do not paper over this.

---

## 4. Size bounds — the analysis behind the budget

Facts from the consuming engine (measured, not guessed):

- **Input granularity:** reliabilities/competences/weights arrive as short
  decimals (≤4 decimal places) — leaf denominators ≤ 10⁴. Evidence counts and
  scale constants are small integers (weights, `W = 2`, dogmatic count 100,
  evidence cap 500).
- **Chain depth per claim:** ~15–20 primitive ops (reliability products, trust
  discount, evidence conversion, decay multiply, meta-claim recursion capped at
  depth 3).
- **Fusion depth:** production caps are 20,000 claims / 1,000 actors; the
  reachable worst case is ~**1,000 sequential binary fusions** on one
  (subject, predicate) — the default dependence mode makes each actor a
  singleton group. Each fusion is ~10 primitive ops.
- **Total sequential ops on any value path:** ≈ 2 × 10⁴ (worst case).

Implications:

1. **Exact ℚ denominators exceed any fixed width** in the worst case
   (post-GCD growth is roughly additive in bits per fusion step: hundreds to
   thousands of bits at depth 1,000). This is WHY arbitrary precision was
   rejected in favor of verified rounding — pure `i128` exactness is not
   provable at the production ceiling, and a verified bignum is a much larger
   project.
2. **Accumulated error at the budget:** ≈ 2×10⁴ ops × 2^-60 ≈ **2^-45.7 ≈
   2×10^-14 relative** — the same precision class as `f64` accumulation, but
   deterministic (fixed evaluation order, bit-exact reproducible) and with a
   *proven* bound instead of folklore.
3. **Typical investigations** (tens of claims, single-digit actors per group,
   short-decimal inputs) stay within budget through most or all of the
   pipeline → R1 makes them largely or fully exact.
4. All engine VALUES are magnitude-bounded: opinions in [0, 1], evidence counts
   ≤ ~10⁵. Nothing approaches the 2^62 magnitude ceiling; the budget pressure
   is entirely in the DENOMINATOR. The `max(1, |exact|)` in R3 is therefore
   effectively absolute error ≤ 2^-60 for opinion-space values.

---

## 5. The f64 boundary (trusted edges, kept minimal)

Exactly two functions touch floats, both at the crate edge, both differentially
tested rather than verified:

- `from_f64_dir` (in): may be implemented exactly — an f64 IS a rational
  `m · 2^e` (53-bit mantissa), so the exact conversion + `round_to_budget` is
  provable with no float reasoning if implemented via `f64::to_bits`
  decomposition on integers. PREFER that (then it is not trusted at all).
  If float intrinsics are used instead, mark `external_body`.
- `to_f64` (out): `external_body`, display/DTO only.

Everything else is integer arithmetic — fully inside the verified region.

---

## 6. Verification obligations (the Verus deliverables, in order)

| # | Obligation | Tier |
|---|---|---|
| V1 | I1 ∧ I2 preserved by every public op (type invariant) | MUST |
| V2 | No panic, no overflow: every i128 intermediate proven in range (overflow checks ON) | MUST |
| V3 | Value correctness vs the ghost model, division-free cross-multiplication specs; exact when no rounding (R1) | MUST |
| V4 | Rounding contract R1–R4 | MUST |
| V5 | GCD (u64 Euclid): correctness (`gcd` divides both, is greatest) + termination (decreasing measure) | MUST |
| V6 | Algebraic laws: `add`/`mul` commutative (always); associative + distributive on the exact path; `Ord` is a total order agreeing with the ghost order; `neg`/`abs`/`recip` involution laws | MUST |
| V7 | Error-propagation (Lipschitz) lemmas: perturbation bounds for add/sub/mul on bounded domain, div with denominator bounded away from 0 — the enabling layer for a future interval type | SHOULD |
| V8 | n-ary helper bounds (`k·2^-B` accumulation) | SHOULD |

Ground rules: **zero `assume`/`admit` in shipping code; every `external_body`
function enumerated in a TRUSTED.md** with its assumed spec and the differential
tests that back it (target: exactly one — `to_f64` — if `from_f64_dir` goes the
bit-decomposition route). `cargo build` (plain rustc) and `verus` verification
must both pass in CI on every commit.

---

## 7. Test harness

- **Oracle:** `malachite-q` as a **dev-dependency only** (LGPL-3.0 is fine for
  test code that is never distributed; it must NEVER appear in the non-dev
  dependency tree — enforce with a CI check). Differential tests: every op,
  random inputs + exhaustive small inputs, assert exact-path results equal the
  oracle and rounded results are within the R3 bound of the oracle's exact
  value.
- **Property tests:** canonicality and I2 after every op; commutativity;
  round-trip `serde`; R1 on constructed-representable cases; determinism
  (byte-identical results across runs/threads).
- **Adversarial fixtures:** budget-edge values (`den = 2^62 − 1`), sign edges,
  `i64::MIN` exclusion (note: `|i64::MIN|` overflows — bound I2 already
  excludes it, but test the constructor rejects/handles it), long fold chains
  (10⁴ ops) with error tracked against the oracle.

---

## 8. Milestones

1. **M1** — `Q` type, ghost model, canonical constructor, verified GCD (V1, V5).
2. **M2** — add/sub/mul/div/neg/abs/cmp with exact-path specs (V2, V3, V6-core).
3. **M3** — rounding: budget detection, dyadic snap, R1–R4 (V4); exactness theorem.
4. **M4** — boundary: `from_f64_dir` (bit-decomposition), `to_f64`, `from_decimal`, serde, Display; TRUSTED.md.
5. **M5** — malachite oracle harness + property tests + CI (verus + cargo + no-LGPL-in-release-tree check).
6. **M6 (stretch)** — V7 Lipschitz lemmas; interval type `QI = [lo: Q, hi: Q]` on the directed modes.

Acceptance = M1–M5 verified and green. The consuming engine rewrite starts
against the M2 API surface and is a separate project.

---

## 9. Corrections found during implementation

*Not part of the original specification. Appended by the implementation so the
spec text and the shipped crate do not disagree silently. The sections above are
unchanged; each entry below says what §N claims, why it does not hold, and what
the crate does instead. All four are documented in `README.md` and
`VERIFICATION.md` as well, and each has a test.*

**§2.1 — `Q::new` cannot be total over `i64` pairs.** The inventory implies that
every `(num, den)` pair fits I2 once reduced. It does not: `Q::new(i64::MAX, 1)`
is already in lowest terms and exceeds the `2^62 − 1` budget. `Q::new` is
therefore partial in two ways — `None` on `den == 0` *and* on an over-budget
reduced form — and `Q::new_rounded` is the total variant, returning `None`
**iff** `den == 0`.

**§3 R3 — the contract is scoped below the magnitude ceiling.** For an exact
value with `|n/d| > 2^62 − 1` the crate declines to state R3, and results
saturate. Note this is a *choice*: it is tempting to say no representable `Q`
could satisfy the bound there, but that is false — `n/d = MAX_MAG + 1/2` is
within `2^-61` of `MAX_MAG/1`. The exclusion keeps the contract on one clean
side of a boundary rather than being forced. R3 is therefore stated under
`!saturated(n, d)`; such results saturate to `±MAX_MAG`,
and `checked_add`/`checked_sub`/`checked_mul` report them as `None` exactly
there (`ensures r.is_none() <==> saturated(...)`).

**§2.5 / V8 — the accumulated bound is absolute, not relative.** The phrasing
`k·2^-B` reads naturally as `k · 2^-B · max(1, |exact|)`, matching R3's shape.
Relative error does not accumulate by induction: the magnitude in the bound is
the magnitude of the *running* sum, which moves at every step, so the induction
hypothesis and the goal quantify over different quantities. The theorem is
stated absolutely instead, carrying an explicit magnitude bound `m` on the
intermediates (`nary::fold_bounded(s, m)` and
`nary::theorem_sum_error_accumulation(s, m)`). For the consuming engine — every
opinion component in `[0, 1]`, so `m == 1` — the two statements coincide. This
is a correction, not a weakening: the relative form is not true as stated.

**§6 V5 — the verified workhorse is `gcd_u128`, not `gcd_u64`.** V5 names "u64
Euclid", but canonicalisation reduces the `i128` intermediates produced by the
arithmetic, not `i64` operands. `gcd_u128` carries the proofs; `gcd_u64` is a
thin verified wrapper kept for the narrow case.
