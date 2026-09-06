# the-q

Bounded rational arithmetic with verified directed rounding, in Rust, proven in
[Verus](https://github.com/verus-lang/verus).

```rust
use the_q::Rat;

let reliability = Rat::from_decimal(85, 2).unwrap();   // 0.85, exactly — 17/20
let weight      = Rat::from_decimal(3, 1).unwrap();    // 0.3,  exactly — 3/10
let combined    = Rat::mul(reliability, weight);       // 51/200, exactly
assert_eq!(combined.to_string(), "51/200");
```

## `Rat` and `Q`

`Rat` is `num / den` in two `i64` fields, always canonical (`den > 0`,
`gcd(|num|, den) == 1`) and always bounded (`|num|, den <= 2^62 − 1`). It is
`Copy`, 128 bits, no heap, `Send + Sync`. The fields are private; every `Rat` a
caller can hold came from a constructor and satisfies the invariant.

`Rat` is exact whenever the exact result fits the budget and rounded when it
does not. It is **partial**: `Rat::new(_, 0)` is `None`; `Rat::div(x, 0)` and
`Rat::zero().recip()` panic (a precondition under Verus, a runtime check with a
message for everyone else); and an exact result above the budget **saturates**
to `±(2^62 − 1)`, which the `checked_*` variants report as `None` and the plain
operations do not.

`Q` makes every one of those cases a value:

```rust
pub enum Q {
    Number(Rat),
    PosSat, NegSat,   // magnitude exceeds the budget; sign known
    PosInf, NegInf,   // exactly infinite
    Nan,              // no information
}
```

Every operation on `Q` — arithmetic, comparison, the folds, every root and
transcendental — is total: it returns a value in the type and never panics.

```rust
use the_q::{Q, Rat, MAX_MAG};

assert_eq!(Q::div(Q::one(), Q::zero()), Q::PosInf);
assert_eq!(Q::div(Q::zero(), Q::zero()), Q::Nan);
let m = Q::Number(Rat::new(MAX_MAG, 1).unwrap());
assert!(Q::add(m, m).is_saturated());
```

Three deliberate choices, each different from IEEE 754:

* `PosSat` denotes the finite reals above the budget, not infinity. So
  `Number(0) * PosSat == Number(0)`, and there is no `is_finite()`.
* The order is total: `Nan == Nan`, and `Nan` sorts last. `Q` can be a map key.
  Outside `Number` the order is on representations, not values.
* `min`/`max`/`clamp` propagate `Nan`, so a fold of `Q::min` is not
  `iter().min()`.

## The rounding contract

When an exact result does not fit, it snaps to a dyadic grid chosen per
magnitude: with `k = bitlen(floor(|x|))`, the grid step is `2^-(62-k)`, capped
at `2^-61`. Ties go to even. Proven, for every operation:

| | |
|---|---|
| R1 | a representable exact result is returned unchanged |
| R2 | `Dir::Down` ≤ exact ≤ `Dir::Up` |
| R3 | error ≤ `2^-61 · max(1, |exact|)` in every direction; `2^-62` for `Dir::Nearest`, which `add`/`sub`/`mul`/`div` use |
| R4 | rounding is monotone on a fixed grid |

R3 is **absolute below 1**. A result near 1 carries ~61 significant bits; a
result near `2^-40` carries ~21; below `2^-62` a value rounds to zero. This is
the single most important thing to know before using the crate for small
quantities, and it governs every accuracy figure below. If small values matter,
scale the problem.

## Limits

**Not associative.** `add` and `mul` are commutative with rounding. They are
associative and distributive only on the exact path (no intermediate rounds),
and that is proven. The general failure is bounded:
`|((a+b)+c) − (a+(b+c))| ≤ 4 · 2^-61 · m` for any bound `m ≥ 1` on the partial
sums, and `|((a·b)·c) − (a·(b·c))| ≤ 6 · 2^-61` on `[0, 1]`.

**Not globally monotone.** R4 holds on each grid, not across the
representable/rounded boundary. Counterexample (`tests/adversarial.rs`):

```text
u = 2 / (2^61 + 1)              representable, returned exactly
v = u · (1 + 1/(2^62 − 2))      a hair larger, not representable
round_down(v) = 2^-61  <  u = round_down(u)       though u < v
```

The cause is that `round` has no single codomain: a representable input is
returned from the whole bounded-denominator set, an unrepresentable one is
snapped to the far coarser dyadic subgrid. Projection onto any one fixed set
would be monotone. Fixing it means either always snapping, which discards
exactness, or a Stern–Brocot floor onto the full set, which is the harder proof.
The crate does neither; if you iterate a rounded projection to a fixed point,
know this.

**Saturation is a choice.** Some exact results above `2^62 − 1` do have a
`Rat` within `2^-61` (`saturation::lemma_saturation_is_a_choice` exhibits one).
R3 is scoped below the ceiling to keep one clean boundary, and results above it
saturate. `Rat::new` also returns `None` for an `i64` pair that is already
reduced but over budget; `Rat::new_rounded` is total in the numerator.

## API

Constructors: `zero`, `one`, `neg_one`, `from_int`, `new`, `new_rounded`,
`from_decimal`, `convert::from_f64_dir`, `convert::from_decimal128_dir` (a
wider `from_decimal`: `i128` mantissa, scale up to 28, directed rounding once
the exact value leaves the budget instead of refusing it).

Arithmetic: `add`, `sub`, `mul`, `div` (nearest, ties to even); `*_dir`
(explicit direction); `checked_*` (`None` on saturation, and on a zero divisor
for `checked_div`); `neg`, `abs`, `recip`, `min`, `max`, `clamp` (exact);
`pow_u32` (a fold of `mul`).

Comparison: `compare`, `eq_q`, `lt`, `le`, `gt`, `ge`, `Ord`/`PartialOrd` —
exact, total. Predicates: `is_zero`, `is_one`, `signum`, `in_unit_interval`.

N-ary (`nary`): `sum`, `product`, `weighted_mean` — fixed left folds, so results
are bit-reproducible across machines and threads.

Intervals (`interval::QI`): `new` (panics on `lo > hi`), `checked_new`, `add`,
`sub`, `mul`, `neg`, `hull`, `contains`, `width` (rounded up; `Q::PosSat` when
too wide to represent), `checked_width`. Enclosure is proven for every sign
pattern.

`Exact` (`exact::Exact`): a `Rat` wrapper whose `add`, `sub`, `mul`, `div`
succeed only when the result needs no rounding, returning
`Result<Exact, ExactError>` (`Inexact`, or `DivisionByZero` for `div`) the
moment it would leave that path — `checked_*` variants return `Option`
instead. Unlike `Rat::checked_*`, which is `None` only on saturation, `Exact`'s
`checked_*` is `None` on *any* rounding, saturating or not. Associativity,
distributivity, and monotonicity, absent in general once rounding happens
(see Limits above), hold for a chain of `Exact` operations whenever every
operation in the chain succeeded — sufficient, not claimed necessary
(`theorem_exact_add_associative`, `theorem_exact_mul_associative`,
`theorem_exact_distributive`, `theorem_exact_add_monotone`,
`theorem_exact_mul_monotone_nonneg`).

Out: `to_f64` (display only; see `TRUSTED.md`), `Display` (`num/den`), serde
(feature-gated; encodes the exact pair).

The `rust_decimal` feature adds `convert::from_rust_decimal_dir` (`Decimal` to
`Rat`, directed) and `convert::q_from_rust_decimal`/`impl From<Decimal> for Q`
(rounds to nearest, saturating by sign past the budget, like `q_from_f64`).
`Decimal`'s own representation is exact (`mantissa · 10^-scale`, no rounding of
its own), so the conversion is exact whenever the reduced pair fits; see
`tests/rust_decimal.rs`.

### Roots and transcendentals, on `Q`

`sqrt`, `cbrt`, `hypot`; `exp`, `exp2`, `powf`, `pow_i32`, `ln`, `log2`,
`log10`, `log`; `sin`, `cos`, `tan`, `asin`, `acos`, `atan`, `atan2`; `sinh`,
`cosh`, `tanh`; constants `pi`, `e`, `ln2`, `ln10`, `half_pi`. All total, all
fixed-length series (termination is structural, cost is constant). They live on
`Q` because none is rational-closed.

Domains: `exp` returns `PosSat` above `x = 43.67` and `0` below `−44`; `sin`,
`cos`, `tan` return `Nan` for `|x| > 2^20`; `sqrt(PosSat)` and `ln(PosSat)` are
`Nan` because the image of the saturated region reaches back inside the budget.

**Accuracy is measured, not proven.** Two independent oracles were used — mpmath
at 120 decimal digits, and exact rational series in Common Lisp carried to
`2^-160` — and they agree with each other to better than `2^-98` on every
function. Worst observed error over the sweeps (`tests/transcendental.rs` and
`scripts/accuracy/`), in R3's own metric `|got − true| / max(1, |true|)`:

| function | worst error | note |
|---|---|---|
| `exp`, `cosh`, `sinh`, `tanh` | `2^-61` | |
| `e` | `2^-63` | |
| `sqrt` | `2^-61` | |
| `hypot` | `2^-62` | |
| `cbrt`, `powf` | `2^-60` | via `exp(ln)` |
| `pi`, `ln2`, `atan2` | `2^-60` | |
| `ln`, `log2` | `2^-59` | |
| `log10` | `2^-61` | |
| `atan`, `asin`, `acos` | `2^-58` | |
| `sin`, `cos`, `tan` | `2^-59` at `|x| ≤ 1`, `2^-57` at `≤ 8`, `2^-50` at `≤ 2^10`, `2^-40` at `≤ 2^20` | reduction error grows as `|x| · 2^-60` |
| `exp2` | `|x| · 2^-61` (`2^-55` at `x = 40`) | argument scaled by a rounded `ln 2` |

Read the table with the R3 caveat above: these are absolute bounds below 1.
`asin(0.002)` is `2^-53` *relative*; `exp(−40)` is `2^-3`; `exp(−44)` is `0`.
`tan` near a pole inherits `cos`'s absolute error divided by `cos²`, so it is
unbounded there. `ln` within `2^-8` of 1 keeps a small-denominator rational and
is often far better than `2^-61` absolute, but not uniformly: `2^-52` relative
at `1 ± 2^-24`, `2^-124` at `1 ± 2^-60`.

`pi`, `e`, `ln2`, `ln10` are literals; each has a `*_series` derivation and a
test that the two are bit-identical.

## What is proven

`1088 verified, 0 errors` in CI; no `assume`, no `admit`; three
`external_body` functions, enumerated in `TRUSTED.md`.

* **V1** Every public operation preserves canonical form and the budget.
* **V2** No panic, no overflow: every `i128` intermediate is bounded. The
  `2^62` budget is exactly what makes cross-multiplied products fit.
* **V3** Every result equals the exact rational model, stated division-free.
* **V4** R1–R4 above, with the tighter nearest bound.
* **V5** GCD correctness and termination.
* **V6** Commutativity; exact-path associativity and distributivity; identity
  and involution laws; a total order agreeing with the value order.
* **V7** Lipschitz bounds for `add`, `mul`, `recip`, `div`.
* **V8** Accumulation bounds: `sum` and `product` within `k · m · 2^-61` after
  `k` steps (`product` needs `|factor| ≤ 1`); `weighted_mean`'s returned value
  within `8k · 2^-61 / δ` when weights and values lie in `[0, 1]` and the exact
  weight sum is at least `δ`.
* **V9** `Q`: totality, classification, total order, `Nan` absorption.
* **V10** Transcendentals: totality and termination. `isqrt` is exactly the
  integer square root.
* The associativity bounds under Limits, interval enclosure, and the value
  pinning of every constructor including the `f64` decomposition's integer
  core.

**Not proven**: the `f64` decode/encode (trusted, tested); transcendental
accuracy (measured, above); `pow_u32`'s value (only its well-formedness);
`mul` associativity outside `[0, 1]`.

## Testing

`malachite-q` is the oracle, as a dev-dependency only (`scripts/check-no-lgpl.sh`
enforces this). `tests/oracle.rs` runs 20,000 random cases per operation per
direction against R1–R3 plus every `p/q` with `|p|, q ≤ 12`; `tests/bounds.rs`
checks R3's nearest bound, the weighted-mean bound and interval enclosure on
random operands; `tests/props.rs` covers the invariant, the laws, and
byte-identical results across eight threads; `tests/adversarial.rs` holds the
budget edges and both counterexamples; `tests/transcendental.rs` carries the
accuracy oracles. Overflow checks stay on in release.

## Performance

`cargo bench --bench arith`: minimum of seven runs, `overflow-checks = true`.
Linux 6.16 x86-64, rustc 1.96. The benchmark prints its own quality block; on
this run control drift was 5.8% and the widest spread 137%, so treat the second
digit as noise.

| op | the-q | `num-rational` `Ratio<i64>` | `malachite-q` (exact) | `f64` |
|---|---:|---:|---:|---:|
| `add` | 56 ns | 127 ns | 110 ns | 1.3 ns |
| `mul` | 62 ns | 150 ns | 147 ns | 1.3 ns |
| `div` | 62 ns | 160 ns | 131 ns | 1.3 ns |
| compare | 2.6 ns | 28 ns | 68 ns | 1.4 ns |

Those are exact-path costs. Rounding is the expensive path, and it is where
the exact backend wins:

| `Rat::add` path | the-q | exact |
|---|---:|---:|
| no rounding | 14 ns | 49 ns |
| rounded | 349 ns | 148 ns |
| saturated | 137 ns | 46 ns |

| chain `acc = (acc + x) · y`, per step | the-q | exact | exact digits |
|---|---:|---:|---:|
| `k = 4` | 195 ns | 326 ns | 29 |
| `k = 64` | 1400 ns | 443 ns | 311 |
| `k = 1024` | 1503 ns | 1093 ns | 2 979 |
| `k = 4096` | 1619 ns | 2609 ns | 8 806 |

`the-q` plateaus once operands fill the budget; the exact backend grows without
bound and is cheaper between roughly `k = 8` and `k = 2000`. An 8-pair
`weighted_mean` is 8.0 µs against 5.3 µs exact. Transcendentals: `exp` 0.6 µs,
`ln` 1.5 µs, `sqrt` 11 µs, `sin`/`cos` 17–19 µs, `atan` 32 µs.

`the-q` is the right tool when memory must be flat, chains are long or
unbounded, or the per-step error must be a proven number. For short exact
computations use an exact rational; for speed use `f64`.

## Verification

Specifications and proofs live in the source inside `verus!` blocks. `cargo
build` compiles them with plain rustc; `cargo verus verify` checks them.
`VERIFICATION.md` has the obligation map and reproduction steps; `TRUSTED.md`
the three trusted functions; `docs/SPEC.md` the original specification with its
six recorded departures.

## Licence

Dual-licensed. Free under AGPL-3.0-or-later: use, modify, and redistribute
freely, including as a network service, as long as you release your source
under the same terms (`AGPL-3.0-or-later` section 13 — the network-use
clause — applies to any service built on this crate, not only to
redistributed binaries). If that obligation does not work for your use —
most commercial and closed-source use — a separate commercial licence is
available; contact the author for terms.

The LGPL-3.0-only oracle `malachite-q` is a dev-dependency only and never
ships, so its terms do not apply to any release of this crate.
