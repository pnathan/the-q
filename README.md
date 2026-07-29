# the-q

Exact-with-verified-rounding rational arithmetic in Rust, specified and proven
in [Verus](https://github.com/verus-lang/verus).

```rust
use the_q::Q;

let reliability = Q::from_decimal(85, 2).unwrap();   // 0.85, exactly — 17/20
let weight      = Q::from_decimal(3, 1).unwrap();    // 0.3,  exactly — 3/10
let combined    = Q::mul(reliability, weight);       // 51/200, exactly
assert_eq!(combined.to_string(), "51/200");
```

`Q` is a rational `num / den` in two `i64` fields, always canonical
(`den > 0`, `gcd(|num|, den) == 1`) and always bounded
(`|num| <= 2^62 - 1`, `den <= 2^62 - 1`) — provided you build it with the
constructors. It is `Copy`, 128 bits, no heap, no allocation, trivially
`Send + Sync`.

The fields are public because Verus cannot state a public invariant about a
datatype whose fields it cannot see. Under Verus that costs nothing: every
operation `requires` the invariant, so a hand-built `Q { num: 3, den: 0 }`
cannot be passed to anything. In unverified Rust it is a footgun — use
`Q::new`, `Q::from_decimal` or `Q::from_int`.

## Why

Subjective-logic fusion — Jøsang cumulative and averaging belief fusion, opinion
algebra — is rational-closed. Implementing it in `f64` throws exactness away for
nothing and buys three problems: results depend on evaluation order, addition
stops being associative, and none of it can be verified. The alternatives were
worse. `malachite-q`, the best bignum rational available, is LGPL-3.0-only,
which is a blocker for statically linked proprietary binaries. And under Verus,
*any* external crate's arithmetic enters the proof as unverified axioms — there
is no verified bignum or verified rational anywhere in the Verus ecosystem
(checked 2026-07; this crate is first of its kind).

So: a **bounded rational with verified directed rounding**. Exact while values
fit a fixed width budget, with machine-stated error bounds when they do not.

## The three things you need to know

**1. Small computations are exact, not approximate.** If every exact
intermediate fits the budget, every operation returns it untouched (R1). A
typical investigation — tens of claims, short-decimal inputs, single-digit
actors per group — never rounds at all. Not "accurate to 15 digits". Exact.

**2. Large computations round, with a proven bound.** When an exact result no
longer fits, it snaps to a dyadic grid chosen per magnitude, and the error is at
most `2^-61 · max(1, |exact|)` (R3). Over the consuming engine's worst case of
~2·10⁴ sequential operations that accumulates to roughly `2^-46.7 ≈ 1·10^-14`
relative — the same precision class as `f64`, except deterministic and *proven*
rather than folklore.

**3. Results are bit-reproducible.** Canonical form means every value has
exactly one bit pattern. Fixed left-to-right fold order in the n-ary helpers
means the same inputs give the same bits on every machine, in every thread, on
every run. The test suite checks this across eight concurrent threads.

## Honesty notes

These are the places where the pretty story has edges. They are documented
because pretending otherwise would make the crate less useful, not more.

### `add` and `mul` are commutative but not associative

Commutativity holds unconditionally, rounding and all: `add(a, b)` and
`add(b, a)` feed provably equal integers into the same rounding function, so
they return the same bits. Proven (`laws::theorem_add_commutative`), and checked
on 50,000 random pairs per direction.

Associativity and distributivity hold **only on the exact path** — whenever no
intermediate rounds. Proven for that case
(`laws::theorem_add_associative_exact` and friends). In general they fail:
rounding the inner sum can land on a different grid point than rounding the
outer one. The test suite contains a test that *searches for* an associativity
failure and fails if it cannot find one, so this note cannot go stale in either
direction.

Consequence for a consuming engine: order-independence claims hold **exactly**
for computations that stay inside the budget, and **up to the accumulated error
bound** otherwise.

### The composed operation is not globally monotone

R4 (monotonicity) is stated **per grid**, which is what the specification
permits, because the composed operation — "return it exactly if it fits,
otherwise snap to the dyadic grid" — is not monotone across that boundary. Here
is the counterexample, which is also a test
(`adversarial::the_composed_operation_is_not_globally_monotone`):

```text
u = 2 / (2^61 + 1)                        representable, so returned exactly
v = u · (1 + 1/(2^62 - 2))                a hair larger, and not representable

both lie inside the grid cell (2^-61, 2·2^-61), so v snaps down to 2^-61
        round_down(v) = 2^-61  <  u  =  round_down(u)

u < v, but rounding down inverted them.
```

The rounding *step itself* is monotone on a fixed grid — that is the claim R4
actually makes, and it is separately tested
(`adversarial::rounding_is_monotone_within_one_grid`). If you need order
preservation across the boundary you need best-approximant (Stern–Brocot)
rounding instead of dyadic snap; that is a strictly harder proof and is not what
this crate does.

### Magnitude overflow saturates

For an exact value whose magnitude exceeds `2^62 - 1`, R3 is declared not to
apply: such results **saturate** to `±(2^62 - 1)`, and `checked_add`,
`checked_sub` and `checked_mul` report the condition as `None`. The exclusion is
a choice rather than a necessity — some unrepresentable values *do* have a `Q`
inside the bound — made to keep the contract on one clean side of a boundary. No engine value comes anywhere
near this ceiling — opinions live in `[0, 1]` and evidence counts top out around
10⁵ — the budget pressure is entirely in the *denominator*. This is a documented
departure from a literal reading of the specification, which states R3
unconditionally.

Relatedly, `Q::new` returns `None` for `i64` pairs above the budget
(`Q::new(i64::MAX, 1)` does not fit), not only for a zero denominator.
`Q::new_rounded` is the total variant: `None` **iff** the denominator is zero.

## Why the budget is `2^62`

Every intermediate is computed exactly in `i128`:

| operation | widest intermediate | bound under I2 | fits `i128`? |
|---|---|---|---|
| `mul` | `num₁·num₂`, `den₁·den₂` | `≤ (2^62−1)² < 2^124` | yes |
| `add`/`sub` | `num₁·den₂ ± num₂·den₁` | `≤ 2·(2^62−1)² < 2^125` | yes |
| `add`/`sub` | `den₁·den₂` | `< 2^124` | yes |
| `cmp` | `num₁·den₂` vs `num₂·den₁` | `< 2^124` | yes |

With a `2^63` budget the addition numerator reaches `2^127`, which overflows
`i128::MAX = 2^127 − 1`. `2^62` leaves two bits of headroom on every row. No
`wrapping_*` appears anywhere in the crate, and the release profile keeps
overflow checks **on**.

The one place the naive approach *would* overflow is the rounding step: it needs
`floor(n · 2^s / d)` where `n · 2^s` can reach `2^185`. That product is never
formed — `round::shift_div` walks `s ≤ 61` doubling steps carrying only a
quotient (`< 2^62`) and a remainder (`< d ≤ 2^124`), so the widest live value is
`2·d < 2^125`.

## How the rounding works

With `k = bitlen(floor(|x|))` — so `2^(k-1) ≤ |x| < 2^k` for `|x| ≥ 1`, and
`k = 0` for `|x| < 1` — the shift is `s = 62 - k`, capped at `61` and floored
at `0`:

* the grid step is `2^-s`, which is `2^(k-62)` for `k ≥ 1` and `2^-61` at the
  cap (`k == 0`) — that is the worst-case error for the directed modes;
* R3 demands `2^-61 · max(1, |x|)`: `2^-61` for `|x| < 1`, and
  `≥ 2^-61 · 2^(k-1) = 2^(k-62)` above.

The two meet exactly, so **`B = 61` is achieved for the directed modes** — one
bit better than the specification's `B >= 60` bar.

`Dir::Nearest`, which every default operation uses, is a *half* grid step and so
actually satisfies `B = 62`. The proofs do not claim it: the contract is stated
uniformly at `B = 61` across all three directions. Tightening `Nearest` would
need a half-step form of `lemma_grid_error_step` (division-free:
`2·|sn·rd − rn·2^s| ≤ rd`). That bit is left on the table deliberately, and
noted here so the gap is visible rather than accidental.

### Why `62 - k` and not `61 - k`

The obvious choice reserves a bit of headroom, keeping `|x| · 2^s < 2^61` so
that a rounding carry can never push the numerator past the budget. That spends
a bit of precision to avoid a case which is cheap to handle directly.

Spending the whole budget gives `|x| · 2^s < 2^k · 2^(62-k) = 2^62`, so rounding
up can land on `2^62` exactly — one past `MAX_MAG`. That is the *carry*, and it
costs nothing: the pair is then `±2^62 / 2^s` with `s ≥ 1`, and `2^s` divides
`2^62`, so the GCD reduction every operation already performs turns it into
`±2^(62-s) / 1`, comfortably inside I2. The proof is `lemma_carry_reduces`.

The cap at `s ≤ 61` is what keeps the *denominator* `2^s` inside the budget in
the `k == 0` case, where no carry is possible anyway.

Ties are broken to even, as IEEE-754 does, so long fold chains do not drift in
a fixed direction.

## API

Constructors: `zero`, `one`, `neg_one`, `from_int`, `new`, `new_rounded`,
`from_decimal`, `convert::from_f64_dir`.

Arithmetic: `add`, `sub`, `mul`, `div` (round-to-nearest, ties to even);
`add_dir`, `sub_dir`, `mul_dir`, `div_dir` (explicit direction); `checked_add`,
`checked_sub`, `checked_mul`; `neg`, `abs`, `recip`, `pow_u32` — all exact;
`min`, `max`, `clamp` — all exact.

`div` and `recip` take `!b.is_zero()` as a **precondition**, discharged by the
caller under Verus. There is no runtime division-by-zero path to panic on.

Comparison: `compare`, `eq_q`, `lt`, `le`, `gt`, `ge`, plus `Ord`/`PartialOrd`.
All exact, no epsilon, and *total* — `ℚ` has no `NaN`, so `partial_cmp` is never
`None`. Predicates: `is_zero`, `is_one`, `signum`, `in_unit_interval`.

N-ary (`nary`): `sum`, `product`, `weighted_mean` — binary left folds in fixed
order, so V2 safety is inherited and results are reproducible.

Intervals (`interval::QI`): `add`, `sub`, `mul`, `neg`, `hull`, `contains`,
`width`. Built on the directed modes; the containment property is a corollary of
R2 and needed no new rounding proofs. A `width` of zero means the computation
never left the exact path — which makes it a measurement of what rounding
actually cost, instead of a worst-case bound.

Out (`convert`): `to_f64` (display/DTO only — see `TRUSTED.md`), `Display`
(`"num/den"`), and feature-gated `serde` that encodes the `(num, den)` integer
pair for exact round-tripping.

### Not provided, deliberately

No transcendental functions of any kind — no `exp`, `ln`, `sqrt`, no rational
exponents. A consuming engine that needs them should compute them as an `f64`
pre-pass and bring the result in through `from_f64_dir`. No arbitrary precision:
that is the escalation path if benchmarks ever show rounding actually biting,
and it is an order-of-magnitude larger verification project.

## Verification

Specifications and proofs live in the source, inside `verus!` blocks.
`cargo build` compiles them with plain rustc (all ghost code is erased);
`cargo verus verify` checks them. See:

* **`VERIFICATION.md`** — the obligation map (V1–V8), what is proven where, and
  the current status of each.
* **`TRUSTED.md`** — every `external_body` function, its assumed specification,
  and the differential tests backing it. There are two.
* **`docs/SPEC.md` §9** — the five places the specification as written does not
  hold, what the crate does instead, and why. Appended rather than edited into
  the spec body, so the original text stays readable.

**Current status: every proof obligation discharges — `482 verified, 0 errors`,
as a required CI check.** No `assume`, no `admit`, two `external_body` functions
at the `f64` edge. `VERIFICATION.md` carries the obligation map, the trajectory,
and the six Verus lessons the work turned up. The executable behaviour is
independently validated by the test suite below.

## Testing

`malachite-q` is the oracle — arbitrary precision, exact, and completely
independent of anything here. It is a **dev-dependency only**;
`scripts/check-no-lgpl.sh` fails CI if it ever appears in the shipped dependency
tree.

* `tests/oracle.rs` — differential tests for every operation: 20,000 random
  cases each against R1, R2 and R3, plus exhaustive coverage of every `p/q` with
  `|p| ≤ 12, q ≤ 12` (90,000 pairs × 4 operations × 3 directions), the `f64`
  boundary, and a 10⁴-operation chain checked against the accumulation bound.
* `tests/props.rs` — invariant preservation, commutativity, exact-path
  associativity and distributivity, total-order axioms, `Hash`/`Eq` agreement,
  serde round-tripping, and byte-identical determinism across eight threads.
* `tests/adversarial.rs` — budget-edge values, sign edges, `i64::MIN`,
  saturation, subnormal doubles, and the two documented counterexamples.

```sh
cargo test --features serde
cargo test --release --features serde     # overflow checks stay on in release
```

## Licence

LGPL-2.1-or-later, matching the repository. The LGPL-3.0-only oracle
`malachite-q` is confined to `[dev-dependencies]` and is never linked into a
shipped artefact.
