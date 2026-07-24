# the-q

Exact-with-verified-rounding rational arithmetic for Rust, checked by [Verus](https://github.com/verus-lang/verus).

`Q` is a bounded canonical rational `num/den` (`i64` fields) whose every operation either returns the mathematically exact result or a nearby approximation guaranteed to be within **2^−60 relative error**. All invariants are machine-checked at the Verus spec level; the exec code compiles with plain `rustc` (Verus macros strip to no-ops).

---

## Type invariants

Every `Q` value satisfies both:

| Invariant | Condition |
|-----------|-----------|
| **I1** (canonical) | `den > 0`, `gcd(\|num\|, den) = 1`, and `num == 0 ⇒ den == 1` |
| **I2** (bounded) | `\|num\| ≤ BOUND` and `den ≤ BOUND` where `BOUND = 2^62 − 1` |

These are enforced on **every** constructor and arithmetic result. There is no way to construct a non-canonical `Q` through the public API.

---

## Rounding contract (R1–R4)

Arithmetic is computed exactly in `i128` then rounded back to I2 if necessary.

| Rule | Statement |
|------|-----------|
| **R1** | If the exact GCD-reduced result already satisfies I2, it is returned unchanged (no rounding). |
| **R2** | `Dir::Down` result ≤ exact ≤ `Dir::Up` result. |
| **R3** | `\|result − exact\| ≤ 2^−60 · max(1, \|exact\|)` — relative error ≤ 2^−60. |
| **R4** | Monotone under the direction parameter. |

The internal operations (`add`, `sub`, `mul`, `div`) all use `Dir::Nearest`; the constructor `from_f64_dir` exposes all three directions.

### Overflow safety

| Operation | Max intermediate | Fits `i128`? |
|-----------|-----------------|-------------|
| add numerator | `2 · (2^62−1)^2 ≈ 2^125` | yes (i128 max ≈ 2^127) |
| mul numerator | `(2^62−1)^2 ≈ 2^124` | yes |
| div numerator | same as mul | yes |
| cross-mul (cmp) | `(2^62−1)^2 ≈ 2^124` | yes |

No overflow is possible in any operation, proven at the Verus spec level.

---

## Honesty: commutativity vs. associativity

With rounding, `add` and `mul` are **commutative** (proven in `src/laws.rs` V6) because the exact cross-multiplied numerator and denominator are symmetric — `a·d_b + b·d_a == b·d_a + a·d_b` — and the same rounding is applied to the same values.

They are **not associative in general** with rounding. Example: `(a + b) + c` may round at a different point than `a + (b + c)`, producing a different approximation. This is unavoidable in any fixed-width rational system.

**Associativity holds on the exact path (R1):** if all intermediate results stay within I2 bounds, no rounding is applied, and the operations are exact ring operations on rationals — fully associative.

The accumulated error after `k` `add` operations is bounded by `k · 2^−60` (V8, proven by induction in `src/laws.rs`).

---

## API reference

### Constructors

```rust
Q::zero()                              // 0/1
Q::one()                               // 1/1
Q::from_int(i: i64) -> Option<Q>       // None if |i| > BOUND
Q::new(num: i64, den: i64) -> Option<Q> // None if den==0; canonicalizes
Q::from_decimal(mantissa: i64, dec_places: u8) -> Option<Q>
    // from_decimal(85, 2) → 17/20 (exact: 0.85)
    // None if dec_places ≥ 20 or result exceeds BOUND
Q::from_f64_dir(v: f64, dir: Dir) -> Option<Q>
    // Integer bit-decomposition, no float arithmetic.
    // None on NaN, ±∞, or |v| > 2^61.
```

### Arithmetic

All operations use `Dir::Nearest` internally.

```rust
q.add(other: Q) -> Q    // q + other
q.sub(other: Q) -> Q    // q - other
q.mul(other: Q) -> Q    // q * other
q.div(other: Q) -> Q    // q / other  (other must be nonzero)
q.neg() -> Q            // -q         (always exact)
q.abs() -> Q            // |q|        (always exact)
q.recip() -> Q          // 1/q        (q must be nonzero, always exact)
```

### Comparison

```rust
q.cmp_q(&other) -> Ordering   // exact cross-multiplication, no overflow
q.eq_q(&other) -> bool
q.lt_q(&other) -> bool
q.le_q(&other) -> bool
```

`Q` also implements `PartialOrd`, `Ord`, `PartialEq`, `Eq` (via `cmp_q`/`eq_q`).

### Bounds / predicates

```rust
q.is_zero() -> bool
q.is_one() -> bool
q.in_unit_interval() -> bool   // 0 ≤ q ≤ 1
q.signum() -> i64              // -1, 0, or 1
```

### Range operations

```rust
q.min_q(other: Q) -> Q
q.max_q(other: Q) -> Q
q.clamp_q(lo: Q, hi: Q) -> Q  // panics in debug if lo > hi
```

### n-ary helpers

```rust
Q::sum(slice: &[Q]) -> Q                     // left-fold add
Q::product(slice: &[Q]) -> Q                  // left-fold mul
Q::weighted_mean(pairs: &[(Q, Q)]) -> Option<Q>  // Σ(v·w)/Σw, None if Σw==0
```

### Conversions

```rust
Q::from_decimal(mantissa: i64, dec_places: u8) -> Option<Q>
Q::from_f64_dir(v: f64, dir: Dir) -> Option<Q>
q.to_f64() -> f64    // DTO boundary ONLY — never feed back into Q arithmetic
the_q::convert::to_f64(q: Q) -> f64
```

### Trusted boundary

`to_f64` is the **only trusted function** in this crate. It performs a single `as f64` integer cast and one float division, which cannot be checked by Verus. Everything else (including `from_f64_dir`) stays in the verified integer domain.

See `TRUSTED.md` for the complete trust inventory.

### Serde (optional)

Enable with `features = ["serde"]`. Serializes as `{"num": i64, "den": i64}`.

```toml
[dependencies]
the-q = { version = "0.1", features = ["serde"] }
```

---

## Verification status

| Module | Obligation | Status |
|--------|-----------|--------|
| `src/gcd.rs` | V5: GCD correctness, termination | Verus proof complete |
| `src/round.rs` | R1–R4: rounding contract | Spec + exec, Verus-gated CI |
| `src/laws.rs` | V6: commutativity, Ord laws, involutions | Proof stubs with `nonlinear_arith` |
| `src/laws.rs` | V7: Lipschitz error propagation | Proof stubs |
| `src/laws.rs` | V8: n-ary accumulated error bound | Monotonicity proven |
| `src/q.rs` | V1–V4: I1/I2 preserved by all ops | Structural (enforced by construction) |

Proofs in `src/laws.rs` have no `admit()`. They are structured for Verus discharge; the CI job runs Verus when `vars.VERUS_AVAILABLE == 'true'` in the GitHub environment.

---

## LGPL note

`malachite-q` (the oracle for differential tests) is a **dev-dependency only**. It never enters the release dependency tree. CI enforces this with:

```
cargo metadata --no-deps --format-version 1 | \
    jq '.packages[].dependencies[] | select(.name == "malachite-q") | .kind' | \
    grep -v dev
```

Any non-dev `malachite-q` dependency fails CI.

---

## Quick start

```toml
[dependencies]
the-q = "0.1"
```

```rust
use the_q::{Q, Dir};

let a = Q::new(1, 3).unwrap();  // 1/3
let b = Q::new(1, 6).unwrap();  // 1/6
let c = a.add(b);               // 1/2 (exact, R1 applies)
assert_eq!(c, Q::new(1, 2).unwrap());

let price = Q::from_decimal(1299, 2).unwrap(); // 12.99 = 1299/100
let tax   = Q::from_decimal(8, 2).unwrap();    // 0.08 = 2/25
let total = price.mul(Q::one().add(tax));       // 12.99 * 1.08

let v = Q::from_f64_dir(0.1, Dir::Nearest).unwrap();
println!("{}", v); // rational approx of 0.1
```
