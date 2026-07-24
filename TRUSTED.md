# Trusted boundary

Everything in `the-q` is integer arithmetic inside the verified region **except
the single function enumerated below**. Per the specification (§5, §6 ground
rules), every trusted (`#[verifier::external_body]`) function is listed here with
its assumed specification and the differential tests that back it.

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
