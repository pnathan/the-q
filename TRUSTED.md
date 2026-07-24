# Trusted (external_body) Functions

This document enumerates every function whose specification is assumed
rather than machine-checked by Verus.

## `Q::to_f64`

**Location:** `src/lib.rs`

**Assumed spec:** Returns an `f64` whose value is the nearest IEEE 754
double-precision approximation to `self.num / self.den`.

**Why trusted:** Proving IEEE 754 rounding correctness in Verus would require
modeling the full float specification. The payoff is low because `to_f64` is
used only at the display/DTO boundary and its output is never fed back into
Q arithmetic.

**Differential tests backing this assumption:**
- `tests/oracle.rs::to_f64_matches_oracle` — compares `Q::to_f64()` against
  `malachite_q::Rational::into::<f64>()` for all small values and a sample
  of random/edge-case values.

## `Q::from_f64_dir` — NOT TRUSTED (informational)

`from_f64_dir` uses `f64::to_bits()` to decompose the IEEE 754
representation into integer sign, exponent, and mantissa, then performs
exact integer arithmetic. No float operations are used in the conversion
path. This function is therefore fully inside the verified region (when
Verus proofs are added) and does NOT need `external_body`.
