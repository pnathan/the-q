# Trusted boundary

Three functions are `#[verifier::external_body]`: Verus takes their `ensures`
on faith. Nothing else is. No `assume(...)` or `admit()` appears in `src/`.
None of the three is on an arithmetic path: `Rat` and `Q` arithmetic,
comparison, canonicalisation and rounding never touch a float or call the
guard.

## 1. `convert::f64_decompose`

```rust
#[verifier::external_body]
pub fn f64_decompose(v: f64) -> (r: Option<(bool, u64, i32)>)
    ensures
        r.is_some() ==> {
            let t = r.unwrap();
            &&& t.1 <= 9007199254740992u64   // 2^53
            &&& -1074 <= t.2 <= 971
        },
```

Verus has no model of `f64::to_bits`. The body is shifting and masking on the
bit pattern; there is no floating-point arithmetic in it.

**Assumed.** The stated bounds, and — not expressible in Verus — that
`(negative, mantissa, exponent)` denotes `v` exactly and `None` is returned
for NaN and the infinities.

**Not assumed.** Everything after. `convert::from_parts_dir` takes the triple,
forms the exact integer pair and hands it to the same `round_frac_exec` every
operation uses; it ensures the full value pin `r == round_frac(...)`, R2, R3,
`!saturated`, and `None` only above the `2^61` ceiling. It also re-checks the
bounds at run time so an unverified caller cannot overflow it. `from_f64_dir`
is the two-line composition and ensures only `wf()`, since no postcondition
mentioning `v` is statable.

**Tests.** `oracle::from_f64_matches_oracle` — R3 (all directions) and R2
against `malachite_q::Rational::try_from(f64)`, an independent IEEE-754
decoder, over 5,000 random doubles and 17 specials; `adversarial::f64_boundary_edges`
— every power of two from `2^-60` to `2^61`, `±0.0`, the smallest subnormal,
rejection at `2^62` and `f64::MAX`, and `0.1_f64` converting to the double,
not to `1/10`.

## 2. `convert::to_f64`

```rust
#[verifier::external_body]
pub fn to_f64(q: Rat) -> f64 {
    (q.numerator() as f64) / (q.denominator() as f64)
}
```

No `ensures`; verified code learns nothing from it and should not call it.
Three roundings, so relative error at most about `3 · 2^-53`.
`oracle::to_f64_is_within_four_ulp` checks 20,000 values. Do not feed the result
back into `Rat`: use serde or `Display`, which are exact.

## 3. `q::require_condition`

```rust
#[verifier::external_body]
pub fn require_condition(condition: bool, msg: &str)
    requires
        condition,
{
    assert!(condition, "{}", msg);
}
```

Called by `Rat::div_dir`, `Rat::recip` and `QI::new`, whose preconditions
verified callers discharge statically, making the call unreachable for them.
For unverified callers it is the panic. It is trusted for its message, not for
any numeric claim: `vstd::pervasive::runtime_assert` has the same contract and
a worse message. `adversarial::div_by_zero_panics` and
`adversarial::recip_of_zero_panics` check it.

## Outside the verified region, not trusted

The standard trait implementations are `#[verifier::external]`: Verus ignores
them and verified code cannot call them, so they add no assumptions. Each
delegates to a verified function: `Ord`/`PartialOrd` to `compare`; the
operators to `add`/`sub`/`mul`/`neg` (and `div` on `Q` only, since `Rat::div`
carries a precondition an operator cannot express); `Display` prints
`num/den` (and `nan`, `inf`, `-inf`, `>max`, `<-max` on `Q`); `FromStr` on
`Q` parses what `Display` prints; serde encodes the `(num, den)` pair and
decodes through `Rat::new`, so a corrupt payload is an error rather than a
malformed value (`Q` uses `deserialize_any` and needs a self-describing
format). `convert::q_from_f64` splits on `is_nan`/`is_infinite`/sign and
delegates to `from_f64_dir`.
