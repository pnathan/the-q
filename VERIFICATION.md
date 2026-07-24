# Verification Status and Roadmap

This document tracks the Verus verification status across milestones.

## Overview

The-Q is designed to be **fully verified in Verus** with zero `assume`/`admit` in shipping code. The implementation proceeds in stages, with verification integrated at each milestone.

## Milestone Status

### M1: Core Type (Current) ✅

**Implemented:**
- ✅ Q type definition and invariants (I1, I2)
- ✅ Canonical constructor with GCD reduction
- ✅ Basic arithmetic (add, sub, mul, div, neg, abs)
- ✅ Comparison and predicates (total order)
- ✅ 39 passing tests (14 unit + 25 property)

**Verification pending (Verus not yet available):**
- V1: Type invariant preservation in all operations
- V2: Overflow safety (i128 intermediate range proof)
- V3: Value correctness specs (ghost model cross-mult)
- V5: GCD correctness and termination
- V6: Algebraic laws (commutativity, associativity, distributivity)

**Blocking issues:** None; code is structurally ready for Verus.

---

### M2: Exact Path Specs

**Goal:** Prove all operations are exact when result fits I2.

**Required Verus work:**
- V3 primary: State value-correctness specs for add/sub/mul/div
- V6 core: Prove commutativity and associativity on exact path
- Proof technique: Division-free cross-multiplication in ghost int model

**Estimated effort:** ~200 LOC Verus proof script

---

### M3: Rounding with Error Bounds

**Goal:** Implement dyadic-snap rounding and prove R1-R4.

**Required Verus work:**
- V4 full: Prove error bound `|result - exact| <= 2^-B * max(1, |exact|)` with B ≥ 60
- V4 monotonicity: Prove `x ≤ y => round(x) ≤ round(y)`
- Loop invariants for rounding algorithm

**Estimated effort:** ~400 LOC Verus proofs (the core of the verification project)

---

### M4: Boundary Conditions & Serialization

**Goal:** Finalize external interfaces.

**Required Verus work:**
- `from_f64_dir`: Prove bit-exact f64 decomposition (or mark external_body)
- `to_f64`: Mark as external_body with assumed spec + differential test evidence
- `from_decimal`: Prove correctness of decimal parsing
- `serde`: Prove round-trip correctness

**Estimated effort:** ~100 LOC

---

### M5: CI + Oracle Harness

**Goal:** Integrate Verus verification into CI.

**Required:**
- Install Verus in CI environment
- `cargo build` must pass (Rust)
- `verus src/lib.rs --verify all` must pass (full verification)
- Malachite oracle differential tests (dev-dependency validation)
- LGPL-3.0 check (non-dev dependencies)

**Estimated effort:** Workflow configuration + CI setup

---

### M6 (Stretch): Interval Arithmetic

**Goal:** Define `QI = [lo: Q, hi: Q]` with verified properties.

**Required Verus work:**
- V7: Lipschitz perturbation lemmas for +, -, * under rounding
- Monotonicity of operations for bracketing

**Estimated effort:** ~300 LOC

---

## Verus Installation

To enable verification locally or in CI:

```bash
# Clone Verus repository
git clone https://github.com/verus-lang/verus.git ~/verus
cd ~/verus

# Install
python3 tools/install-deps.sh
./build.sh

# Verify this project
verus /path/to/the-q/src/lib.rs --verify all
```

For CI, add a step to install Verus in the GitHub Actions workflow.

---

## Proof Architecture

### Ghost Model (from spec.rs)

All specs use **unbounded mathematical integers** for clarity:

```
QGhost { num: int, den: int }   // Ghost only, never computed

// Example spec (division-free via cross-mult):
fn spec_add_result(
    a_num: int, a_den: int,
    b_num: int, b_den: int,
    r_num: int, r_den: int,
) -> bool {
    // r = a + b
    r_num * (a_den * b_den) == (a_num * b_den + b_num * a_den) * r_den
}
```

### Invariant Predicates

```rust
fn is_canonical(num: i64, den: i64) -> bool {
    den > 0 && gcd(|num|, den) == 1
}

fn is_bounded(num: i64, den: i64) -> bool {
    |num| <= 2^62 - 1 && den <= 2^62 - 1
}
```

### Verus Skeleton (spec_proofs.rs)

The `spec_proofs.rs` module documents proof obligations:
- Each obligation is named (V1–V8)
- Proof technique is outlined
- Loop invariants and termination measures are indicated

---

## Testing Strategy

### Before Verus (M1–M4)

1. **Unit tests:** Correctness on known inputs
2. **Property tests:** Invariant preservation, algebraic laws
3. **Determinism tests:** Reproducibility across runs
4. **Differential tests:** Against malachite-q oracle (dev-dependency)

### With Verus (M5+)

1. **Verus proofs:** Mechanically checked
2. **Property tests:** Still run as sanity checks
3. **Differential tests:** Archive as validation report (removed from CI if needed for LGPL)

---

## Known Limitations

### Current (M1)

- No formal proof of V1, V2 (tested instead)
- Rounding is conservative placeholder (rounds to bounds)
- Error bounds stated but not proven
- `from_f64_dir` is stub implementation

### By M5

- All MUST obligations (V1–V6) formally proven
- Error bounds (R1–R4) proven with B = 60
- to_f64 marked external_body; backed by differential tests

### Stretch (M6+)

- SHOULD obligations (V7, V8) proven
- Interval type with Lipschitz guarantees

---

## References

- **Verus documentation:** https://verus-lang.github.io/
- **Lean formalization (parent project):** Uses similar division-free spec style
- **SMT solver notes:** Cross-mult avoids SMT division instability
- **Rounding:** Error bound formula from "Handbook of Floating-Point Arithmetic"

---

**Last updated:** 2026-07-24  
**Verification framework:** Verus (to be installed)  
**Current proof status:** Structural outline complete; formal proofs pending Verus availability
