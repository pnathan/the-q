# Trusted boundary

`src/lib.rs` is now verified directly by Verus (`verus --crate-type=lib
src/lib.rs`, a CI hard gate): the whole file is wrapped in `verus! { … }` and the
invariant model + API contracts are checked on the exec functions.

## Trusted set during the port (being tightened)

While the direct port is completed, some heavy internal bodies carry
`#[verifier::external_body]` — Verus checks their **signatures/contracts**
(e.g. `ensures wf(r)`) but trusts their **bodies**. Their mathematical content is
independently machine-checked at the `int` level under `verus/` (V1–V8), and
their behavior is covered end-to-end by the `malachite-q` differential oracle
(60k+ cases). The current trusted-body set is:

- `round_to_budget`, `from_dyadic`, `scaled_floor`, `reduce_i128`, `gcd_u128`,
  `bits` — the rounding/canonicalization internals (proofs: `verus/src/
  verified_round*.rs`, `verified_reduce.rs`, `verified_gcd.rs`, `verified_uniq.rs`,
  `gcd_checked.rs`).
- the constructors/predicates whose bodies do integer field arithmetic
  (`zero`/`one`/`from_int`/`new`/`from_decimal`/`neg`/`abs`/`recip`/`eq`/`is_zero`/
  `is_one`/`signum`/`in_unit_interval`/`numer`/`denom`/`min`-adjacent helpers) and
  the n-ary folds (`sum`/`product`/`weighted_mean`).
- `from_f64_dir` — see below.

**End goal:** remove `external_body` from all of the above (porting each proof
from its `verus/` transcription onto the exec body), leaving the trusted set at
exactly `to_f64`.

## The permanent trusted function

Per the specification (§5, §6 ground rules), the permanently trusted
(`#[verifier::external_body]`) function is listed here with its assumed
specification and the differential tests that back it.

## Target: exactly one trusted function

`the-q` meets the "exactly one trusted boundary" target because
[`Q::from_f64_dir`] takes the **bit-decomposition route** (§5): an `f64` is
decomposed with `f64::to_bits` into an exact `± mantissa · 2^exp` and rounded
with integer-only `round_to_budget`. It touches no floating-point arithmetic and
is therefore **inside** the verified region — *not* trusted.

## `Q::to_f64(self) -> f64`  — TRUSTED

- **Role.** Display / DTO boundary only. Converts a canonical `Q` to the nearest
  representable `f64`. Its result must **never** be fed back into `Q`
  arithmetic (doing so would reintroduce the non-determinism this crate exists
  to eliminate).
- **Why trusted.** Proving IEEE-754 round-to-nearest of `num / den` in Verus is
  not worth the cost for a display-only edge; the function is marked
  `#[verifier::external_body]` in the Verus mirror.
- **Assumed spec.** `to_f64(q)` returns a finite `f64` equal to the
  IEEE-754-round-to-nearest of the exact rational `q.num / q.den`. For any `q`
  whose value is exactly representable as an `f64` (all `q` with `|value| < 2^53`
  and a power-of-two denominator `<= 2^53`), the result is **exact**.
- **Differential tests that back it** (`tests/`):
  - exact-representable cases (`1/2`, `-3/4`, integers) assert bit-exact equality
    (`unit_tests::to_f64_roundish`);
  - the round-trip `Q -> f64 -> Q` is *not* claimed (lossy by design) and is not
    tested as a round-trip;
  - the CI differential harness confirms `to_f64` is monotone and never panics
    across the random sweep (it is only ever read at the display edge).

## Non-trusted float edge (documented for completeness)

`Q::from_f64_dir(v, dir)` — **NOT trusted**. Implemented via `f64::to_bits`
integer decomposition + `round_to_budget`. Covered by
`unit_tests::from_f64_exact_dyadic` / `from_f64_directed_brackets` and the oracle
harness. If a future change replaces the bit-decomposition with a float-intrinsic
implementation, it must be marked `#[verifier::external_body]` and added to this
file.

## Rule

`ci/verify.sh` greps the Verus sources for `external_body` and fails if any
occurrence is not documented in this file. Zero `assume`/`admit` is required in
any proof promoted to "complete" (see `verus/README.md`).
