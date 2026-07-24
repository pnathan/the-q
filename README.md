# the-q

**Verified bounded rational (ℚ) arithmetic with directed rounding.**

`the-q` is a `no_std`, dependency-free (in its release tree) Rust crate providing
exact-with-verified-rounding rational arithmetic, designed to be machine-checked
by [Verus](https://github.com/verus-lang/verus). It is the deterministic numeric
backbone for a subjective-logic fusion engine — a rewrite of an `f64` engine
whose results were non-deterministic across evaluation orders, non-associative,
and unverifiable.

There is no verified bignum or rational anywhere in the Verus ecosystem; this is
first-of-kind. The design is a **bounded rational with verified directed
rounding**: exact arithmetic while values fit a fixed width budget, and
machine-checked error bounds when they don't.

## Representation

```rust
pub struct Q { num: i64, den: i64 }   // value = num / den
```

Every value is stored **canonically** and satisfies two invariants, established
and preserved by every public operation:

- **I1 (canonical):** `den > 0`, `gcd(|num|, den) == 1`, `num == 0 ⟹ den == 1`.
- **I2 (bounded):** `|num| ≤ 2^62 − 1` and `den ≤ 2^62 − 1`.

Canonical form means **structural equality is mathematical equality**, so
`Eq`/`Hash` are derived and every value has one bit-exact representation. `Q` is
`Copy` (a plain 128-bit value, no heap, trivially `Send + Sync`).

### Why `2^62`, not `2^63`

All intermediate computation is exact in `i128`. Under I2 the worst intermediate
— the add numerator `num₁·den₂ + num₂·den₁` — is `< 2^125`, comfortably inside
`i128::MAX = 2^127 − 1`. A `2^63` budget would push it to `2^127` and overflow.
The `2^62` budget guarantees **no arithmetic panic or overflow is possible** with
overflow checks on (verification obligation V2).

## Quick start

```rust
use the_q::{Q, Dir};

let a = Q::from_decimal(85, 2).unwrap();   // 0.85 = 17/20
let b = Q::new(1, 3).unwrap();             // 1/3
let c = a.add(b);                          // exact: 71/60
assert!(c.eq(Q::new(71, 60).unwrap()));

// Total order (an upgrade over f64's PartialOrd):
assert!(Q::new(3, 4).unwrap().gt(Q::new(5, 7).unwrap())); // 0.75 > 0.714…

// Directed rounding for a future interval layer:
let lo = a.mul_dir(b, Dir::Down);
let hi = a.mul_dir(b, Dir::Up);
assert!(lo.le(hi));
```

## The rounding contract

When an exact result exceeds the budget, it is snapped to the dyadic grid
`p / 2^s` (with `s` chosen per magnitude). The contract, proven per operation:

- **R1 (identity on representables):** if the exact reduced result fits the
  budget, the op returns it **exactly**. *Consequence (theorem): any computation
  whose exact values all fit the budget is end-to-end exact — small
  investigations pay zero rounding.*
- **R2 (directed):** `Dir::Down` result ≤ exact ≤ `Dir::Up` result.
- **R3 (error bound):** `|result − exact| ≤ 2^-60 · max(1, |exact|)`  (B = 60),
  for `|exact| ≤ 2^62 − 1`. Larger magnitudes cannot be represented within the
  budget at all; they saturate to `±(2^62 − 1)/1`. The engine's value domain
  (opinions in `[0, 1]`, counts `≤ 10^5`) never approaches this — the budget
  pressure is entirely in the *denominator*, never the value magnitude — so
  saturation is a safety net, not a path the engine exercises.
- **R4 (monotone):** `x ≤ y ⟹ round(x, dir) ≤ round(y, dir)`.

Default ops (`add`, `sub`, `mul`, `div`) round to **nearest**; the directed
variants (`*_dir`) exist so an interval layer can bracket without new proofs.

## Honesty consequence — read this

With rounding enabled:

- `add` and `mul` are **commutative** (always — proven).
- `add` and `mul` are **NOT associative in general**. Associativity and
  distributivity hold **only on the exact path** (when no operand or result is
  rounded) — and that is proven too.

So the consuming engine's order-independence claims hold **exactly** for small
cases and **up to the accumulated error bound** in general. At the production
ceiling (~2×10⁴ sequential ops) the accumulated error is ≈ 2^-45.7 ≈ 2×10⁻¹⁴
relative — the precision class of `f64`, but **deterministic** (fixed evaluation
order, bit-exact, reproducible across runs and threads) and with a **proven**
bound instead of folklore. This is not papered over; it is the point.

## API surface

- **Constructors:** `zero`, `one`, `from_int`, `new`, `from_decimal`,
  `from_f64_dir`.
- **Arithmetic:** `add`/`sub`/`mul`/`div` (+ `*_dir` directed variants), `neg`,
  `abs`, `recip`, `min`, `max`, `clamp`, `checked_div`.
- **Comparison / predicates (exact, total):** `eq`, `lt`, `le`, `gt`, `ge`,
  `cmp_q` / `Ord`, `is_zero`, `is_one`, `signum`, `in_unit_interval`.
- **Out / plumbing:** `to_f64` (display/DTO only — see `TRUSTED.md`), `Display`,
  optional `serde` (feature `serde`, encodes the `(num, den)` pair for exact
  round-trip), `Hash`/`Eq`/`Ord`/`Clone`/`Copy`.
- **n-ary helpers:** `sum`, `product`, `weighted_mean` (fixed-order binary
  folds).

Out of scope by design: transcendental functions and arbitrary precision (see
the crate specification).

## Verification & trust

- **Verified region:** all integer arithmetic. Proof scaffold under `verus/`
  (obligations V1–V6; see `verus/README.md` for per-obligation status).
- **Trusted boundary:** exactly one function, `to_f64` — documented with its
  assumed spec and backing tests in `TRUSTED.md`.
- **Oracle:** `malachite-q` as a **dev-dependency only** (its LGPL-3.0 license is
  fine for test code that is never distributed; CI enforces it never enters the
  release dependency tree).

### Building and testing

```sh
cargo build                 # plain rustc, no Verus needed, no_std
cargo test --all-features   # unit + malachite differential + property/adversarial
```

> **Verus status:** the machine-checked proofs are authored but not yet
> discharged in this repository's initial drop — the environment that created it
> could not install the Verus toolchain. `cargo build`/`cargo test` are the
> enforced CI gate today; the `verus` job runs the proofs and currently reports
> progress without blocking. See `verus/README.md`.

## License

LGPL-2.1-only (see `LICENSE`).
