# Trusted surface

Ground rule: **zero `assume` / `admit` anywhere.** `grep -rn "assume(\|admit()" src/`
comes back empty, and CI enforces it. Everything below is the *complete*
enumeration of code and specifications that the Verus proofs do not cover.

## 1. `external_body` functions

### `Q::to_f64` (src/float.rs)

```rust
#[verifier::external_body]
pub fn to_f64(self) -> f64 { (self.num as f64) / (self.den as f64) }
```

- **Assumed spec:** none (no `ensures`). The function is documented as
  *display/DTO boundary only* and must never be fed back into `Q`
  arithmetic (the only way back in is `from_f64_dir`, which re-rounds with
  a verified contract).
- **Actual behavior:** two int→float roundings plus one float division,
  each correctly rounded per IEEE-754; the result is within a few ulp of
  the true rational value.
- **Backing tests:** `tests/oracle.rs` compares `to_f64` against
  malachite-q's correctly-rounded rational→f64 conversion on random and
  adversarial inputs and asserts closeness (≤ 4 ulp).

### `f64_bits` (src/float.rs, private)

```rust
#[verifier::external_body]
fn f64_bits(v: f64) -> (r: u64) ensures r == f64_to_bits(v) { v.to_bits() }
```

- **Assumed spec:** `f64::to_bits` agrees with Verus's *builtin* ghost
  model `verus_builtin::f64_to_bits`. This is the definition of `to_bits`
  in the Rust reference; the wrapper exists only because vstd does not yet
  ship an `assume_specification` for the exec method.
- Everything downstream of the bit pattern — sign/exponent/mantissa
  extraction (done with `/` and `%`, no bit tricks), exact rational
  construction, budget rounding — is **verified**, so `from_f64_dir` is
  *not* on the trusted list.
- **Backing tests:** differential tests against malachite-q's exact
  `Rational::try_from(f64)` on random bit patterns and IEEE edge cases
  (subnormals, powers of two, max/min, ±0).

## 2. Spec fidelity (definitions the proofs are *relative to*)

These are not code, but definitions an auditor should read:

- **IEEE-754 decode** (`f64_sign_neg` … `f64_den`, src/float.rs): the
  spec-level decode of a binary64 bit pattern into an exact rational.
  A mistake here would make `from_f64_dir`'s theorem vacuous. It is ~30
  lines of arithmetic, mirrors the standard field layout, and is exercised
  by the same differential tests as above.
- **Ghost model** (`q_eq`/`q_le`, `gcd`, `pow2`, invariant `inv`): standard
  textbook definitions, stated division-free by cross-multiplication.

## 3. Unverified glue (no arithmetic, delegates only)

`src/traits.rs` — outside the `verus!` macro, therefore unverified by
construction, and deliberately free of arithmetic:

| Item | Delegates to | Note |
|---|---|---|
| `Hash` | `to_parts` (verified, total) | field hash; sound because canonical form makes structural equality mathematical equality (`lemma_canonical_unique`) |
| `PartialOrd`/`Ord` | `cmp_q` (verified) | `cmp_q`'s precondition is the type invariant, which every constructed `Q` satisfies |
| `Display`/`Debug` | `to_parts` | formatting only |
| `serde` (feature-gated) | `to_parts` / `Q::new` | deserialization re-canonicalizes through the verified constructor, so the invariant holds for all deserialized values and serialize→deserialize round-trips exactly |

`PartialEq`/`Eq`/`Clone`/`Copy` are `derive`d on the struct (structural),
which is semantically correct by `lemma_canonical_unique`.

## 4. Toolchain

As with any Verus development, the TCB includes Verus itself, Z3, rustc,
and vstd's axiomatization of primitive types. CI pins
Verus `release/0.2026.07.12.0b42f4c` (and the matching crates.io `vstd`).
