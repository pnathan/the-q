# Verification Status and Roadmap

This document tracks the Verus verification status across milestones.

## Verus Setup (Local Development)

### Prerequisites
- Rust 1.96.0+ with rustup
- git
- curl
- Z3 4.12.5 (downloaded automatically by Verus build script)

### Installation

1. Clone the Verus repository:
   ```bash
   git clone --depth 1 https://github.com/verus-lang/verus.git ~/verus
   cd ~/verus/source
   ```

2. Run the Z3 setup script:
   ```bash
   bash tools/get-z3.sh
   ```

3. Activate the development environment:
   ```bash
   source ../tools/activate  # bash/zsh
   source ../tools/activate.fish  # fish
   ```

4. Build Verus:
   ```bash
   export VERUS_Z3_PATH=/path/to/z3/binary
   vargo build --release
   ```

### Running Verification

From the the-q project root:

```bash
./scripts/verify-with-verus.sh
```

This script:
- Checks for vargo availability
- Sets up Z3 path automatically
- Runs Verus on src/verus_verify.rs
- Reports verification results

Expected output:
```
verification results:: 5 verified, 0 errors
```

---

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

**Verus Setup & Verification:** ✅
- ✅ Verus installed and building from source locally
- ✅ Created src/verus_verify.rs with core specifications
- ✅ Verified: 5 verified, 0 errors
- ✅ Local verification via: `./scripts/verify-with-verus.sh`
- ✅ Z3 4.12.5 installed and integrated

**Verification Status:**
- ✅ Specifications created (V1-V6 placeholders)
- ⏳ Lemma proofs pending detailed implementation (V1-V6 full proofs)
  - V1: Type invariant preservation in all operations
  - V2: Overflow safety (i128 intermediate range proof)
  - V3: Value correctness specs (ghost model cross-mult)
  - V5: GCD correctness and termination
  - V6: Algebraic laws (commutativity, associativity, distributivity)

**Blocking issues:** None; Verus infrastructure is ready for detailed proofs.

---

### M2: Exact Path Specs ⏳

**Goal:** Prove all operations are exact when result fits I2.

**Implementation plan:**
1. Extend `src/verus_verify.rs` with lemmas for each operation:
   ```verus
   proof fn add_exact_spec(a_num: i128, a_den: i128, b_num: i128, b_den: i128, r_num: i128, r_den: i128)
       requires is_canonical(a_num as i64, a_den as i64, 1) && is_bounded(a_num as i64, a_den as i64)
       requires is_canonical(b_num as i64, b_den as i64, 1) && is_bounded(b_num as i64, b_den as i64)
       ensures spec_add_result(a_num, a_den, b_num, b_den, r_num, r_den)
   ```

2. Prove commutativity and associativity using cross-mult:
   - `a + b == b + a` via symmetry of multiplication
   - `(a + b) + c == a + (b + c)` via associativity in ghost int

**Testing strategy:**
- Property tests remain as pre-proof validation
- Verus proofs are primary correctness evidence
- Differential tests against malachite-q (dev-only)

**Verification obligations:**
- V3: Value correctness (add, sub, mul, div)
- V6: Algebraic laws (commutativity, associativity, distributivity)

**Estimated effort:** ~200 LOC Verus proof script

**Timeline:** M2 is prerequisite for M3

---

### M3: Rounding with Error Bounds ⏳

**Goal:** Implement dyadic-snap rounding and prove R1-R4 error bounds.

**Algorithm (dyadic-snap):**
```rust
fn round_dyadic_snap(exact_num: i128, exact_den: i128, bits: u32) -> Q {
    // 1. Compute exact rational value at 2^-bits precision
    // 2. Round to nearest dyadic (snap to grid)
    // 3. Reduce to canonical form
    // 4. Clamp to bounds if needed
}
```

**Verus proofs required:**
- **R1 (Correctness on exact):** If result fits I2, result is exact
- **R2 (Correctness on overflow):** Overflow path produces bounded result
- **R3 (Error bound):** `|rounded - exact| <= 2^-B * max(1, |exact|)` with B ≥ 60
- **R4 (Monotonicity):** `x ≤ y => round(x) ≤ round(y)`

**Loop invariants for rounding loop:**
- Bit position counter strictly decreases
- Running result maintains invariants I1, I2
- Error accumulation bounded by target

**Testing:**
- Property tests: monotonicity, idempotence on exact inputs
- Fuzzing: random rationals with random bit widths
- Edge cases: zero, infinity (clamped), subnormal values

**Verification obligations:**
- V4: Full error bound proof with loop invariants
- V1, V2: Overflow analysis for rounding intermediate values

**Estimated effort:** ~400 LOC Verus proofs (largest proof milestone)

**Timeline:** Depends on M2 completion

---

### M4: Boundary Conditions & Serialization ⏳

**Goal:** Finalize external interfaces with verified correctness or external_body declarations.

**Implementation targets:**

**from_f64_dir:**
- Extract sign, exponent, mantissa from f64 bits
- Convert to canonical Q representation
- Verus option 1: Full bit-exact proof
- Verus option 2: Mark `external_body` + property test validation

**to_f64:**
- Convert Q to nearest f64
- Mark as `external_body` (transcendental, unsafe)
- Backing: Differential tests against malachite-q (dev-only)
- Spec: `|to_f64(q) - q| <= ε_mach * |q|`

**from_decimal:**
- Parse ASCII decimal string to Q
- Prove correctness of decimal coefficient → denominator power mapping
- Example: "3.14" → Q(314, 100) → Q(157, 50)

**serde (feature-gated):**
- Round-trip correctness: `deserialize(serialize(q)) == q`
- Canonical form preservation
- Tests: JSON, bincode, MessagePack if supported

**Testing strategy:**
- Unit tests: Known f64↔Q mappings
- Property tests: Arbitrary f64 round-trip
- Oracle comparison: malachite-q round-trip equivalence

**Verification obligations:**
- V8 (SHOULD): External boundary correctness (except external_body items)
- V1: Canonical form preserved through serialization

**Estimated effort:** ~150 LOC (100 Rust + 50 LOC Verus proof/annotations)

**Timeline:** Can proceed in parallel with M3

---

### M5: CI Integration & Oracle Harness ✅ (Infrastructure Ready)

**Goal:** Integrate Verus verification into GitHub Actions CI.

**Current status (M1):**
- ✅ Verus verification script created: `./scripts/verify-with-verus.sh`
- ✅ VERIFICATION.md setup instructions documented
- ✅ Local verification working: 5 verified, 0 errors

**CI workflow updates needed for M5:**
1. **Verus caching:** Cache Verus build (~15min save per run)
   - Store `target-verus/release/verus` binary
   - Cache vstd verification state

2. **Verification gates:**
   - `cargo build` must pass (always)
   - `cargo test` must pass (always)
   - `verus src/verus_verify.rs` must pass (non-blocking M2–M4)
   - `verus src/lib.rs --verify all` must pass (required M5+)

3. **Oracle harness (dev-only):**
   - Run malachite-q differential tests after main verification
   - Generate validation report (optional archive)
   - Do NOT block merge on oracle (reference implementation, not spec)

4. **LGPL tracking:**
   - Continue LGPL-3.0 dependency check
   - malachite-q remains dev-only

**CI job structure:**
```yaml
jobs:
  build:
    - cargo build --all
    - cargo test --all
  verus:
    - ./scripts/verify-with-verus.sh
    - verus src/lib.rs --verify all  # Depends on M2-M4
  lint:
    - cargo fmt --check
    - cargo clippy --all
  lgpl-check:
    - Check dependencies
```

**Estimated effort:** ~50 LOC workflow YAML + caching setup

**Timeline:** Parallel with M2–M4; finalize in M5

---

### M6 (Stretch): Interval Arithmetic & Uncertainty ⏳

**Goal:** Define verified interval type `QI = [lo: Q, hi: Q]` for uncertainty propagation.

**Type definition:**
```rust
pub struct QI {
    pub lo: Q,    // Lower bound (always ≤ upper)
    pub hi: Q,    // Upper bound
}

impl QI {
    pub fn point(q: Q) -> Self { QI { lo: q, hi: q } }
    pub fn interval(lo: Q, hi: Q) -> Result<Self, Error> { ... }
    pub fn add(&self, other: &QI) -> QI { ... }
    pub fn mul(&self, other: &QI) -> QI { ... }
    pub fn recip(&self) -> Result<QI, Error> { ... }  // Requires 0 ∉ [lo, hi]
}
```

**Verus proofs:**
- **V7 (Lipschitz bounds):** Prove perturbation lemmas for interval operations
  - Add: `|add(x, y) - add(x', y')| <= Lip_x * |x - x'| + Lip_y * |y - y'|`
  - Mul: Similar with product rule
  - Recip: Bounds depend on distance from zero

- **V8 (Monotonicity):** Operations preserve interval order
  - `lo1 ≤ lo2 ∧ hi1 ≤ hi2 ⟹ add(...) ordered correctly`

**Testing:**
- Unit tests: Basic interval arithmetic
- Property tests: Interval containment (computed result ⊇ exact result)
- Uncertainty propagation: Physics-style error analysis examples

**Estimated effort:** ~300 LOC Verus + 200 LOC Rust

**Timeline:** Post-M5; architectural foundation only in M1–M5

**Use cases (future):**
- Numerical algorithm validation
- Uncertainty quantification in simulations
- Certified approximation algorithms

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

## CI Monitoring & Failure Handling

### Automated CI Checks

The GitHub Actions workflow (`/.github/workflows/ci.yml`) runs on every push and PR:

1. **Build step:** `cargo build --all` (Rust compiler)
2. **Test step:** `cargo test --all` (39/39 tests)
3. **Format check:** `cargo fmt -- --check`
4. **Lint check:** `cargo clippy --all -- -D warnings`
5. **Verus verification:** `./scripts/verify-with-verus.sh` (non-blocking M1–M4)
6. **LGPL check:** Verify malachite-q in dev-dependencies only

### Expected CI Results

**M1 (Current):**
- ✅ All cargo checks pass
- ✅ Verus script produces: `verification results:: 5 verified, 0 errors`
- ✅ No LGPL violations

**M2–M4:**
- ✅ Cargo checks
- ⏳ Verus verification grows (more lemmas added)
- ⏳ Test for rounding algorithm

**M5:**
- ✅ All checks required to pass (no continue-on-error)

### Failure Diagnosis

**If `cargo build` fails:**
- Check Rust compiler version (should match `rust-toolchain.toml`)
- Verify dependencies: `cargo tree`
- Run locally: `cargo build --all`

**If `cargo test` fails:**
- Run failing test locally: `cargo test <test-name>`
- Check if test was recently added or modified
- Verify test doesn't depend on external state

**If `cargo fmt` or `cargo clippy` fails:**
- Auto-fix: `cargo fmt` (then commit)
- Clippy: Review suggestion and fix or add `#[allow(...)]`

**If Verus verification fails:**
- Check Verus installation: `source ../tools/activate && vargo build --release`
- Run locally: `./scripts/verify-with-verus.sh`
- Review proof errors in output
- Update spec or proof as needed

**If LGPL check fails:**
- Ensure `malachite-q` is in `[dev-dependencies]`, not `[dependencies]`
- Check `Cargo.toml` section ordering

### Monitoring Strategy

**For developers:**
- Watch branch for CI status via GitHub PR checks
- Subscribe to notifications on this repo
- Manual check: `./scripts/verify-with-verus.sh` before pushing

**For CI automation:**
- GitHub Actions runs on every push to `claude/**` branches
- CI results appear as PR checks (required for merge)
- Failures block merge until resolved

### Verus-Specific Monitoring

**During M2–M6 proof development:**
1. **Incremental proof additions:** Add one lemma at a time
2. **Test each lemma:** `verus src/verus_verify.rs` before committing
3. **Commit message:** Include verification status
   ```
   Add lemma: commutativity of addition
   
   Verus: 6 verified, 0 errors
   ```

4. **PR template:** Note verification progress
   ```
   ## Verification Status
   - V3 (value correctness): 40% implemented
   - V6 (algebraic laws): 80% implemented
   - Verus: 12 verified, 0 errors
   ```

---

## References

- **Verus documentation:** https://verus-lang.github.io/verus/guide/getting_started.html
- **Verus proof examples:** https://github.com/verus-lang/verus/tree/main/examples
- **Lean formalization (parent project):** Uses similar division-free spec style
- **SMT solver notes:** Cross-multiplication avoids SMT division instability
- **Rounding:** Error bound formula from "Handbook of Floating-Point Arithmetic" (Muller et al.)
- **Interval arithmetic:** "Interval Arithmetic: From Principles to Implementation" (Kulisch & Miranker)

---

**Last updated:** 2026-07-24  
**Verification framework:** Verus (installed and working locally)  
**Current proof status:** M1 specifications verified (5/5); formal lemma proofs pending M2–M6 implementation
