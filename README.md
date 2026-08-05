# the-q

Exact-with-verified-rounding rational arithmetic in Rust, specified and proven
in [Verus](https://github.com/verus-lang/verus).

```rust
use the_q::Rat;

let reliability = Rat::from_decimal(85, 2).unwrap();   // 0.85, exactly — 17/20
let weight      = Rat::from_decimal(3, 1).unwrap();    // 0.3,  exactly — 3/10
let combined    = Rat::mul(reliability, weight);       // 51/200, exactly
assert_eq!(combined.to_string(), "51/200");
```

`Rat` is a rational `num / den` in two `i64` fields, always canonical
(`den > 0`, `gcd(|num|, den) == 1`) and always bounded
(`|num| <= 2^62 - 1`, `den <= 2^62 - 1`) — provided you build it with the
constructors. It is `Copy`, 128 bits, no heap, no allocation, trivially
`Send + Sync`.

The fields are public because Verus cannot state a public invariant about a
datatype whose fields it cannot see. The type is `#[non_exhaustive]`, so that
visibility costs nothing either way: `Rat { num: 3, den: 0 }` does not compile
outside the crate, and `Rat::new`, `Rat::new_rounded`, `Rat::from_decimal` and
`Rat::from_int` are the only way in. Each canonicalises what it is given.

## Two types: `Rat` and `Q`

`Rat` above is the verified kernel — exact, canonical, bounded, and **partial**.
`Rat::new(_, 0)` is `None`, `Rat::div(x, 0)` and `Rat::zero().recip()` panic
rather than return, and `Rat::add(MAX_MAG, MAX_MAG)` silently returns `MAX_MAG`
— wrong by a factor of two and indistinguishable from a real answer.

`Q` layers explicit non-representable states over that kernel, so that "not a
representable rational" becomes an observable state instead of something the
caller is trusted to have ruled out:

```rust
pub enum Q {
    Number(Rat),
    PosSat, NegSat,   // magnitude exceeds the budget; sign known
    PosInf, NegInf,   // exactly infinite
    Nan,              // no information
}
```

Arithmetic on `Q` is **total**: every operation on every input returns a value
in the type, and nothing panics.

```rust
use the_q::{Q, Rat, MAX_MAG};

assert_eq!(Q::div(Q::one(), Q::zero()), Q::PosInf);   // not a panic
assert_eq!(Q::div(Q::zero(), Q::zero()), Q::Nan);
assert_eq!(Q::checked_div(Q::one(), Q::zero()), None); // what std does

let m = Q::Number(Rat::new(MAX_MAG, 1).unwrap());
assert!(Q::add(m, m).is_saturated());                  // reported, not clamped
```

Three things about the design are easy to get wrong and are worth stating up
front:

* **Saturation is not infinity.** `PosSat` denotes `(MAX_MAG, +∞)` — genuinely
  finite reals above the budget — while `PosInf` denotes `{+∞}`. Keeping them
  apart is what lets `is_saturated()` mean "an overflow happened" and
  `is_infinite()` mean "a division by zero happened". It also makes
  `Number(0) * PosSat` exactly `Number(0)`, where `0 * ∞` is genuinely
  indeterminate. For the same reason there is deliberately **no `is_finite()`**:
  a saturated value *is* finite, so that would be the wrong axis.

* **The order is total, and that costs a second IEEE departure.** `Nan == Nan`
  is true, and `Nan` sorts last. IEEE makes every ordered comparison involving
  NaN false, which is exactly what forbids a total order — `f64` sidesteps this
  by having no `Ord` at all. The trade here goes the other way, so `Q` can be a
  `BTreeMap` key or be sorted directly. Outside `Number` the order is on
  *representations*, not denoted values.

* **`min`/`max`/`clamp` propagate `Nan` and therefore disagree with
  `Ord`-based selection.** A fold of `Q::min` is **not** `slice.iter().min()`.
  Deriving selection from the order would give `min(Nan, Number(5)) ==
  Number(5)` — asserting the value is exactly 5 when it could be anything. IEEE
  fought this out and withdrew `minNum`/`maxNum` in 754-2019 for the same
  reason.

The design, including the full propagation tables and the reasoning behind each
cell, is issue #26. `Rat` keeps its invariant verbatim, so every proof
obligation that existed before this layer still discharges with its exact
original statement.

## What never panics, and what still does

`Q`'s entire public surface is total: arithmetic, comparison, the predicates,
the folds, and every root and transcendental. There is no input — including
zero divisors, values past the budget, and every special state — for which any
of them panics or returns a malformed value. Verus discharges the no-panic
obligation over the whole module, and the test suite re-checks it on the
compiled artifact by sweeping every function over every state plus tens of
thousands of random values.

`Rat` is deliberately **not** total. `Rat::new(_, 0)` is `None`, and
`Rat::div(x, 0)` and `Rat::zero().recip()` panic. That is the point of the
split: `Rat` is the verified kernel where preconditions are discharged
statically at the call site, and `Q` is the layer that makes them into values
for callers who cannot. If you want the guarantee, use `Q`.

What `Rat` does **not** do is return a wrong answer to an unverified caller. It
is `#[non_exhaustive]`, so no other crate can build a `Rat` from a struct
literal and the constructors are the only way in; the two preconditioned
operations check at the boundary and panic instead of computing on a value they
were never given; and `Rat::checked_div` is total in the divisor, returning
`None` for a zero divisor as `i64::checked_div` does. Every reachable `Rat` is
canonical and in budget.

There are no `assume(...)` or `admit()` calls anywhere in the shipping code.

## Performance, measured

`cargo bench` runs the numbers below (minimum of seven timed runs, deterministic
inputs, `release` with `overflow-checks = true` — the configuration the crate
actually ships, not a faster one).

| operation | the-q | f64 | ratio | before Stein |
|---|---:|---:|---:|---:|
| `Rat::add` / `sub` | 160 ns | 3.2 ns | 50× | 273 ns |
| `Rat::mul` / `div` | 156 ns | 3.3 ns | 47× | 260 ns |
| `Q::add` (total) | 186 ns | 5.4 ns | 34× | 261 ns |
| `Q::div` (total) | 172 ns | 5.1 ns | 33× | 235 ns |
| `Q::compare` | 7.8 ns | 5.8 ns | **1.3×** | 9.3 ns |

Three things worth reading off that table. **Totality is nearly free** — `Q::add`
costs about 15% more than the partial `Rat::add`, so the explicit
non-representable states are a type-level win rather than a runtime tax.
**Comparison is in the same class as `f64`**, because it is integer
cross-multiplication with no floating-point classification to do. And the last
column is the cost of the gcd algorithm: canonicalisation runs a gcd on every
result, and Euclid's algorithm needs a remainder, which at `u128` width is a
software routine rather than an instruction. Stein's binary algorithm needs only
halving, comparison and subtraction, and it took approximately 40% off every
operation in the crate. The proofs are in `src/gcd.rs`; the postcondition is
unchanged, so nothing downstream moved.

The remaining ~50× is the price of canonical form: the gcd itself, which is
what makes structural equality mathematical equality and results bit-reproducible
across machines. Against the exact arbitrary-precision alternative the crate is
*faster* at depth — an exact rational's denominators grow without bound, and by a
4096-step fusion chain it is slower than `the-q` while carrying 8806-digit
numerators.

### Transcendentals

| function | the-q | f64 (hardware) | before Stein |
|---|---:|---:|---:|
| `sqrt` | 12.8 µs | 2.9 ns | 20.5 µs |
| `sin` / `cos` | 22.7 µs | ~12 ns | 32.6 µs |
| `ln` | 28.9 µs | 9.3 ns | 40.2 µs |
| `exp` | 30.7 µs | 8.8 ns | 41.4 µs |
| `atan` | 36.8 µs | 9.7 ns | 53.3 µs |

These are software series over exact rationals against silicon, so the ratio is
large and will stay large. Tens of microseconds is usable for fusion and
scoring work; it is not usable in an inner loop that needs millions of
transcendental evaluations per second, and this crate will not pretend
otherwise.

Two rounds of benchmark-driven tuning are already in: `pi`, `e` and `ln2` are
pinned constants rather than series recomputed per call (each proven
bit-identical to its derivation by a test), and every series is sized from its
own tail bound rather than sharing one length — `sin` needs eleven terms where
`atan` needs thirty, because factorial denominators converge far faster than
`1/(2k+1)`. Together those cut `sin` and `cos` by 60%, `atan` by 45% and `ln`
by 40%, with **no change to any measured accuracy figure** — the removed terms
were contributing nothing.

### Accuracy, measured against an exact oracle

| function | worst observed relative error |
|---|---|
| `e` | 2⁻⁶² |
| `sqrt`, `ln2` | 2⁻⁶⁰ |
| `pi`, `exp` (small args) | 2⁻⁵⁹ |
| `ln`, `atan`, `sin²+cos²−1` | 2⁻⁵⁸ |
| `sin`, `cos` | 2⁻⁵⁶ |
| `exp` (full range) | 2⁻⁵³ |

Every one of those is at or better than `f64`'s 2⁻⁵³. The caveat is in the
next section, and it matters more than the table does.

### Where precision runs out

R3's bound is `2^-61 · max(1, |exact|)` — **absolute** below 1, not relative.
A value near 1 carries about 61 significant bits; a value near 2⁻⁴³ carries
about 18. So `exp(-30)` is accurate to only ~2⁻¹⁸ relatively, and
`ln(exp(-30))` comes back off by about 5e-6. Neither function is at fault: the
intermediate could not carry the information. If small values matter, scale the
problem so they are not small.

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

That failure is bounded, not just acknowledged. `laws::theorem_add_associativity_bound`
proves `|((a+b)+c) - (a+(b+c))| <= 4 * 2^-61 * m`, where `m` is a caller-supplied
bound on `max(1, |exact value|)` for every partial sum the two bracketings
touch — no `[0, 1]` assumption required. `laws::theorem_mul_associativity_bound_unit_interval`
proves the multiplicative analogue, `|((a*b)*c) - (a*(b*c))| <= 6 * 2^-61`,
under the hypothesis that `a, b, c` all lie in `[0, 1]` (the engine's actual
domain): `mul`'s error is weighted by the *other* factor's magnitude at each
step rather than simply adding, so a general `m`-parameterised bound would
grow with `m²`, not `m`, and `[0, 1]` is where that distinction collapses.
`tests/adversarial.rs` checks both bounds on a genuine associativity-failure
instance found by the same search.

Consequence for a consuming engine: order-independence claims hold **exactly**
for computations that stay inside the budget, and **up to a proven, explicit
error bound** otherwise — not merely "up to some unquantified accumulated
error".

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
`checked_sub`, `checked_mul` and `checked_div` all report the condition as
`None`. Division saturates on the same ceiling as the other three —
`(MAX_MAG/1) / (1/MAX_MAG)` is well past it — so `checked_div` closes the family
rather than leaving it asymmetric.

The exclusion is a choice rather than a necessity: some unrepresentable values
*do* have a `Rat` inside the bound, and `saturation::lemma_saturation_is_a_choice`
proves it by exhibiting one. Scoping R3 below the ceiling keeps the contract on
one clean side of a boundary; it is not that nothing could satisfy it.

No engine value comes anywhere near this ceiling — opinions live in `[0, 1]` and
evidence counts top out around 10⁵ — so the budget pressure is entirely in the
*denominator*. This is a documented departure from a literal reading of the
specification, which states R3 unconditionally.

Relatedly, `Rat::new` returns `None` for `i64` pairs above the budget
(`Rat::new(i64::MAX, 1)` does not fit), not only for a zero denominator.
`Rat::new_rounded` is the total variant: `None` **iff** the denominator is zero.

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
actually satisfies `B = 62`. The uniform R3 contract stays at `B = 61` across
all three directions — the directed modes genuinely achieve no better — but
`Dir::Nearest` additionally carries the tighter bound as its own proved
guarantee: `Rat::add`, `Rat::sub`, `Rat::mul` and `Rat::div` each `ensures`
`within_error_bound_nearest` alongside the uniform `within_error_bound`. The
proof is the half-step form of the grid-error lemma
(`round::lemma_grid_error_step_nearest_half`, division-free:
`2·|sn·rd − rn·2^s| ≤ rd`), composed the same way R3 itself is
(`round::lemma_r3_error_nearest`).

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
`checked_sub`, `checked_mul`, `checked_div`; `neg`, `abs`, `recip` — all exact;
`pow_u32` — a fold of rounding `mul`, so it rounds as soon as the exact power
leaves the budget, and underflows to `0` for a small enough base (`(1/3)^40`);
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

### Roots and transcendentals — on `Q` only

These live on `Q`, not on `Rat`, because none of them is rational-closed:
`sqrt(2)`, `exp(1)` and `sin(1)` are irrational, so the answer is the nearest
representable rational with a stated error bound, and the out-of-domain cases
need a state to land in. `Rat` has neither.

Roots: `sqrt`, `cbrt`, `hypot`. Exponentials and logarithms: `exp`, `exp2`,
`powf`, `pow_i32`, `ln`, `log2`, `log10`, `log`. Trigonometric: `sin`, `cos`,
`tan`, `asin`, `acos`, `atan`, `atan2`. Hyperbolic: `sinh`, `cosh`, `tanh`.
Constants: `pi`, `e`, `ln2` and `ln10` are pinned literals, each with a
`*_series` derivation and a test asserting the two are bit-identical; `half_pi`
is `pi/2`.

Every one is **total** — `sqrt` of a negative is `Nan`, `ln(0)` is `NegInf`,
nothing panics — and every one is a fixed-length series or iteration, so
termination is structural and the cost of a call is constant. Accuracy and
timings are in the two tables above; the precision floor for results far below
`1` is in "Where precision runs out", and it matters more than the accuracy
table does.

### Not provided, deliberately

No arbitrary precision. That is the escalation path if benchmarks ever show
rounding actually biting, and it is an order-of-magnitude larger verification
project.

No transcendentals on `Rat` itself, for the reason above. A caller working in
`Rat` that wants one should move to `Q`, or compute it as an `f64` pre-pass and
bring the result in through `from_f64_dir`.

## What is proven

Everything below is a machine-checked Verus obligation in this repository, not a
design intention. `871 verified, 0 errors`, no `assume`, no `admit`. Three
`external_body` functions are the only things taken on trust, and `TRUSTED.md`
enumerates them: two at the `f64` edge, and one runtime check that computes
nothing and is trusted for its panic message.

**Representation — every public operation, no exceptions** (V1, V5)

* I1: results are canonical — `den > 0` and `gcd(|num|, den) == 1`.
* I2: results are in budget — `|num| ≤ 2^62 − 1` and `den ≤ 2^62 − 1`.
* `Rat::wf()` is `requires`d of every input and `ensures`d of every output, so the
  invariant is a precondition of the next call rather than a claim about it.
* GCD correctness *and* termination, for the whole module.

**No panic, no overflow** (V2)

* Every `i128` intermediate is proven in range. This is what the `2^62` budget
  is *for*: it is the largest bound under which the cross-multiplied products
  cannot overflow `i128`.

**Value correctness** (V3)

* Every operation's result equals the exact rational model value, stated
  division-free by cross-multiplication — the specification never divides, so
  there is no rounding hidden inside the specification of rounding.

**The rounding contract R1–R4** (V4)

| | claim |
|---|---|
| R1 | rounding is the identity on values already representable |
| R2 | `Dir::Down` ≤ exact ≤ `Dir::Up` |
| R3 | error ≤ `2^-61 · max(1, |exact|)`, uniformly across all three directions |
| R3⁺ | error ≤ `2^-62 · max(1, |exact|)` for `Dir::Nearest` specifically — a half grid step, so one bit better than the directed modes |
| R4 | rounding is monotone on the grid |

**Algebraic laws** (V6)

* `add` and `mul` are commutative — unconditionally, rounding included.
* Associativity and distributivity hold exactly whenever no intermediate rounds
  (`theorem_add_associative_exact`, `theorem_mul_associative_exact`,
  `theorem_distributive_exact`), with the "no intermediate rounds" side
  condition itself a proven predicate rather than an assumption.
* Identity elements, total-order axioms (so `Ord` is a genuine total order — no
  NaN, no incomparable pairs), `neg`/`abs`/`recip` involutions,
  `sub == add ∘ neg`, `div == mul ∘ recip`.

**The associativity defect, quantified**

Not associative is a weak statement. These make it a number:

* `|((a+b)+c) − (a+(b+c))| ≤ 4 · 2^-61 · m` for a free, caller-chosen magnitude
  `m` — no domain restriction.
* `|((a·b)·c) − (a·(b·c))| ≤ 6 · 2^-61` on `[0, 1]`.

So order-independence goes from *void once rounding occurs* to *holds to within
about 10⁻¹⁸ on opinion values*.

**Error propagation** (V7)

* `add`/`sub` are exactly 1-Lipschitz in each argument: errors add.
* Product bound: `|a·b − a'·b'| ≤ (ca·e₂ + cb·e₁)` given `|a| ≤ ca`,
  `|b'| ≤ cb`; on `[0, 1]` both constants are `1` and the errors simply add.
* Reciprocal bound: `|1/b − 1/b'| ≤ e₂·md²/(ed·mn²)` for `b, b' ≥ mn/md > 0`.
  The `md²` is the real quadratic cost of perturbing a divisor.
* Quotient bound, composed from those two — division is multiplication by the
  reciprocal.

**N-ary accumulation** (V8)

| helper | bound after `k` elements | hypothesis |
|---|---|---|
| `sum` | `k · m · 2^-61` | — |
| `product` | `k · m · 2^-61` | every factor's magnitude ≤ 1 |
| `weighted_mean` weight accumulator | `k · m · 2^-61` | — |
| `weighted_mean` numerator accumulator | `2k · m · 2^-61` | — |

The numerator accumulates at twice the rate because each pair costs two
roundings, a `mul` then an `add`. `product`'s hypothesis is not cosmetic:
multiplication is 1-Lipschitz only when weighted by the *other* operand's
magnitude, so a factor above 1 amplifies carried error geometrically and no
uniform `k · 2^-61` bound survives.

Also proven: a fold that never rounds is exact, and all three helpers are pinned
to a spec *function* of their input — reproducibility is a theorem, not a
property of the current code.

**Ingestion — what the constructors produce, not just that it is well-formed**

Every entry point now pins its own value, which until recently none of them did:

* `Rat::new` says what it returns *and* that it returns something: any pair with
  both components inside the budget succeeds. Without that second half the
  contract was satisfied by an implementation returning `None` every time.
* `Rat::from_decimal` is exactly `mantissa / 10^dec_places`, and is `None` exactly
  when `dec_places > 18` or `|mantissa| > MAX_MAG` — both checkable by the
  caller.
* `Rat::new_rounded` is pinned to `round_frac` of its input, with R2 and R3
  against that input under the usual `!saturated` scope.
* `convert::from_parts_dir` — the verified core of `from_f64_dir` — is pinned to
  `round_frac` of the exact rational the IEEE-754 triple denotes, with R2, R3,
  the discharge of R3's own `!saturated` side condition, and `None` only above
  the documented `2^61` ceiling.

The last one covers the whole exponent range in one postcondition, including the
tail below `2^-125` where the denominator `2^s` is larger than `round_frac_exec`
itself accepts and the code takes a shortcut instead of calling the rounder;
`lemma_round_frac_subgrid` proves that shortcut lands where `round_frac` would
have. (The cutoff is on the exponent, not the magnitude: a value below `2^-62`
with `e >= -124` — say `2^-100` — still goes through the ordinary rounder.)

**Intervals**

* `QI::add`, `sub` and `mul` `ensure` well-formedness, so interval results
  compose without re-establishing anything. `mul` needs no narrowed
  precondition and no sign case analysis.
* Enclosure: for `x ∈ a` and `y ∈ b`, the exact `x+y`, `x−y` and `x·y` lie
  within the computed interval — the product case for **every** sign pattern.
* Value postconditions on `width` and `hull`.

**One negative result**

`lemma_saturation_is_a_choice` proves that excluding the region above the
magnitude ceiling from R3 is a *scoping decision, not a necessity*: it exhibits
a value up there that a well-formed `Rat` does satisfy R3 for. The tempting
opposite claim was written into this crate three times by two authors and
corrected twice, so it is now a proof obligation instead of a comment.

### Not proven — stated so it cannot be mistaken for covered

* **The `f64` boundary.** `f64_decompose` and `to_f64` are `external_body`.
  Proving them means proving IEEE-754 semantics, which `docs/SPEC.md` §5 puts
  out of scope. They are backed by shrinking property tests instead. Note the
  boundary is now exactly one step wide: everything *downstream* of the
  decomposed triple is proven — see the ingestion entry above — and
  `from_f64_dir` is a two-line composition of the trusted step with it.
* **`weighted_mean`'s returned value.** Both internal accumulators are bounded;
  composing them through the final division into one bound on what the function
  returns is now *unblocked* (the quotient bound above is the piece that was
  missing) but not done. It additionally needs a weight-sum-bounded-away-from-
  zero hypothesis.
* **`pow_u32`** `ensures` only `wf()`. No value postcondition — it is proven
  not to break the type, not proven to compute a power.
* **A general `mul` associativity bound outside `[0, 1]`.** Multiplication's
  error is weighted by the other factor's magnitude at each step, so the general
  form grows with `m²` rather than `m`. `[0, 1]` is where that collapses to a
  constant.
* **N-ary reordering beyond three terms**, for either operator.

## Verification

Specifications and proofs live in the source, inside `verus!` blocks.
`cargo build` compiles them with plain rustc (all ghost code is erased);
`cargo verus verify` checks them. See:

* **`VERIFICATION.md`** — the obligation map (V1–V8), what is proven where, and
  the current status of each.
* **`TRUSTED.md`** — every `external_body` function, its assumed specification,
  and the tests backing it. There are three.
* **`docs/SPEC.md` §9** — the six places the specification as written does not
  hold, what the crate does instead, and why. Appended rather than edited into
  the spec body, so the original text stays readable.

**Current status: every proof obligation discharges — `871 verified, 0 errors`,
as a required CI check.** No `assume`, no `admit`, three `external_body`
functions: two at the `f64` edge, one a runtime check. `VERIFICATION.md` carries the obligation map, the trajectory,
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

## Performance

`cargo bench` (`benches/arith.rs`) measures `the-q` against the two things it
sits between: hardware `f64`, and `malachite-q`'s arbitrary-precision `Rational`
— the same crate used as the differential oracle. Minimum of seven runs,
deterministic inputs, `bench` profile (which inherits `release`, so
`overflow-checks = true` is *on*: these are the numbers for the configuration
the crate actually ships).

**Single operations, operands with denominators under 10⁴**

| op | the-q | f64 | exact | q/f64 | exact/q |
|---|---|---|---|---|---|
| `add` | 156.3 ns | 3.3 ns | 91.8 ns | 47.9× | 0.6× |
| `sub` | 163.7 ns | 3.0 ns | 95.5 ns | 54.3× | 0.6× |
| `mul` | 149.4 ns | 3.3 ns | 120.7 ns | 45.8× | 0.8× |
| `div` | 162.6 ns | 3.3 ns | 120.2 ns | 48.5× | 0.7× |
| compare | 5.0 ns | 2.9 ns | 41.0 ns | 1.7× | 8.2× |

On *one* operation with small operands, an exact rational is cheaper than
`the-q`, and both cost tens of times an `f64` op. That comparison is not the
interesting one, because it is the one case where an exact rational is cheap.

**Chained fusion — `acc = (acc + x) · y`, cost per step at depth `k`**

| depth | the-q | f64 | exact | q/f64 | exact/q | size of exact result |
|---|---|---|---|---|---|---|
| `k = 4` | 415.0 ns | 5.7 ns | 314.9 ns | 72.4× | 0.8× | 29 digits |
| `k = 16` | 1624.2 ns | 5.1 ns | 361.1 ns | 318.3× | 0.2× | 88 digits |
| `k = 64` | 2074.4 ns | 5.0 ns | 421.3 ns | 412.7× | 0.2× | 311 digits |
| `k = 256` | 2137.7 ns | 4.9 ns | 574.7 ns | 434.2× | 0.3× | 947 digits |
| `k = 1024` | 2120.9 ns | 4.8 ns | 1058.4 ns | 444.0× | 0.5× | 2 979 digits |
| `k = 4096` | 2202.2 ns | 4.8 ns | 2459.0 ns | 455.9× | 1.1× | 8 806 digits |

This is the whole argument for the crate, and it does not flatter it.

`the-q` **rises and then plateaus**: 415 ns/step at `k = 4`, then flat within 4%
from `k = 256` to `k = 4096`. The rise is not the chain getting longer, it is the
operands getting *wider* — a few steps in, numerator and denominator fill the
62-bit budget, so the GCD and the rounding division run at full width on every
subsequent step. Once they do, depth stops mattering. Same 16 bytes at `k = 4`
as at `k = 4096`. Stein's algorithm took roughly a third off this column too:
the same chain cost 3 148 ns/step at `k = 64` under Euclid.

The exact backend does not plateau, because it cannot: its result is 8 806
decimal digits at `k = 4096` and still growing. It is **cheaper than `the-q`
between roughly `k = 8` and `k = 2000`**, and more expensive outside that
window — increasingly so, without limit.

`f64` is flat at ~5 ns and roughly 450× faster than `the-q`. That number is
the price, and it is not small.

**`weighted_mean` over 8 (weight, value) pairs**

| the-q | f64 | exact |
|---|---|---|
| 12.4 µs | 21.2 ns | 5.0 µs |

### What the numbers mean

`the-q` is not the fast option and is not sold as one. It is bounded: 16 bytes
and a fixed worst-case step cost at any depth, where the exact rational's cost
and memory grow with the length of the computation and `f64` gives up exactness
immediately. If a chain is short, an exact rational is both faster and exact —
use one. `the-q` earns its place when chains are long or unbounded, when the
memory has to be flat, or when the error needs to be a *proven* `2^-61` per step
rather than folklore.

```sh
cargo bench --bench arith
```

## Licence

LGPL-2.1-or-later, matching the repository. The LGPL-3.0-only oracle
`malachite-q` is confined to `[dev-dependencies]` and is never linked into a
shipped artefact.
