# TRUSTED.md — Enumeration of trusted (unverified) boundaries

This file lists every function in `the-q` that is **not formally verified by Verus**
and explains the assurance substitute for each.

---

## 1. `convert::to_f64`

```rust
pub fn to_f64(q: Q) -> f64
```

**What it does:** Converts a canonical bounded Q to `f64` for display or DTO
purposes only.

**Why not verified:** Proving IEEE 754 rounding behavior in Verus would require
axiomatizing the float standard. The cost is not justified; this function is
a display/serialization boundary, never fed back into Q arithmetic.

**Assurance substitute:** Differential tests in `tests/oracle.rs` (`from_f64_dir_exact_dyadic`)
check that `to_f64(from_f64_dir(v, Nearest)) ≈ v` for all sampled values.
The function body is a single division of two exact integers — the only possible
error is IEEE 754 rounding of the final division, which is within 0.5 ULP by
the standard.

**Assumed spec:**
```
ensures |to_f64(q) - (q.num as real / q.den as real)| ≤ 0.5 ULP(q.num as real / q.den as real)
```

---

## 2. No other trusted boundaries

`from_f64_dir` is implemented via `f64::to_bits()` (integer decomposition) —
it performs **no float arithmetic** and is fully within the verified region.

`from_decimal`, all arithmetic ops (`add`, `sub`, `mul`, `div`), comparison,
`gcd_exec`, `round_to_budget` — all operate purely on integer types and are
formally verified.

---

## Coverage commitment

Every future function that touches `f64` or calls `external_body` must be added
to this file before merging. The CI check `grep -r 'external_body' src/` must
match exactly the entries here.
