# Trusted Boundary — LGPL Status and External Functions

## Trusted (External) Functions

This crate contains **one** trusted external function that is NOT formally verified in Verus:

### `Q::to_f64(self) -> f64`

**Location:** `src/q.rs:297`

**Assumed spec:** Converting a Q to f64 follows IEEE 754 rounding. This is proven correct via differential tests against malachite-q, not via Verus. The assumption is safe because:

1. **f64 is a rational:** Every f64 is exactly `m * 2^e` (53-bit mantissa, 11-bit exponent), so the conversion is well-defined.
2. **Limited scope:** Used only for display, logging, and DTO serialization; never fed back into Q arithmetic.
3. **Backed by tests:** The property test suite verifies round-trip consistency.

**Why not verified:**
- Proving IEEE 754 in Verus is out of scope for this crate (requires modeling floating-point semantics, a larger undertaking).
- The boundary is narrow and guarded: `to_f64()` is output-only; no Q-valued operation consumes floats without explicit `from_f64_dir()`.

---

## LGPL-Licensed Dependency Scope

### Development-Only Dependency: `malachite-q`

- **License:** LGPL-3.0-only
- **Used in:** `tests/` (dev-dependency only)
- **NOT linked into:** any binary or library release
- **Rationale:** Serves as an oracle for differential testing during development

### Enforcement

The CI check verifies that `malachite-q` does NOT appear in:
- `[dependencies]` (main dependency tree)
- Any binary that ships to end users
- Any artifact licensed under a non-GPL license

Allowed: Test-only and benchmarking usage.

---

## Migration Path

If this crate is ever bundled with GPL-incompatible proprietary code, the Oracle Test Suite (M5) must be:

1. **Run once** during development (to validate implementations against malachite-q)
2. **Archived** as a differential test report
3. **Removed** from shipping CI; replaced with property tests only

This ensures the shipping binary is fully LGPL-free while development can leverage high-quality oracles.

---

## Assumptions Summary

| What | Assumed | Backed By | Risk |
|---|---|---|---|
| IEEE 754 rounding in `to_f64()` | Yes | Differential tests + IEEE 754 spec | Low (external boundary only) |
| GCD correctness | No (proven in tests, Verus proof pending) | Euclidean algorithm + tests | Low |
| i128 overflow soundness | No (proven in tests, Verus proof pending) | Arithmetic analysis + tests | Low (fixed-width analysis) |
| malachite-q correctness | (Oracle only, not trusted) | Peer-reviewed crate | N/A (dev-only) |

---

**Updated:** 2026-07-24  
**Crate version:** 0.1.0 (M1 milestone)
