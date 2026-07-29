# Trusted boundary

Everything in `the-q` is verified integer arithmetic **except** the two
functions below. Each is marked `#[verifier::external_body]`, which means Verus
takes its `ensures` clause on faith and never looks at the body. Each is listed
here with the specification that is being assumed and the tests that check the
assumption against reality.

There are no `assume(...)` or `admit()` calls anywhere in the shipping code.
Grep for them: `rg 'assume\(|admit\(' src/` returns nothing.

Both trusted functions sit at the crate's `f64` edge. Neither is on any
arithmetic path — `Q + Q`, `Q * Q`, comparison, canonicalisation and rounding
never touch a float.

---

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

**Why it is trusted.** Verus has no model of `f64::to_bits`. The body is six
lines of shifting and masking on the raw `u64` bit pattern; there is no
floating-point *arithmetic* in it at all, but the correspondence between an
`f64` and its IEEE-754 encoding is outside what Verus can reason about.

**What is assumed.** Two things:

1. The stated numeric bounds on the returned mantissa and exponent (this is what
   the `ensures` clause says, and it is what downstream verified code relies on
   for its own overflow arguments).
2. That `(negative, mantissa, exponent)` denotes the real value of `v`, i.e.
   `v == (-1)^negative · mantissa · 2^exponent`, and that `None` is returned
   exactly for NaN and the two infinities. This part is *not* expressible in the
   `ensures` clause, because there is no Verus term for "the real value of this
   `f64`". It is an assumption in the ordinary English sense.

**What is not assumed.** Everything downstream. Given the triple,
`convert::from_parts_dir` builds an exact integer pair (`mantissa · 2^e` over
`1`, or `mantissa` over `2^-e`) and hands it to the same `round_frac_exec` that
every arithmetic operation uses. R2 and R3 are therefore proven against the
decomposed rational — the trusted step is only the identification of that
rational with the float.

That sentence used to name `from_f64_dir`, and was **stronger than the code
carried**: `from_f64_dir` ensured only `wf()`, so R2 and R3 appeared nowhere in
the verified contract and rested on the differential tests. The fix was to make
the claim true rather than to soften it. The integer core is now
`convert::from_parts_dir`, which `ensures`

* `r == round_frac(parts_num(neg, mant, e), parts_den(e), dir)` — the full value
  pin, not merely properties of the result;
* R2 (`q_le_frac`/`q_ge_frac` for the directed modes) and R3
  (`within_error_bound`) against that same rational;
* `!saturated(...)` whenever it returns, so R3's own scope condition is
  discharged rather than passed on;
* and that `None` happens *only* above the documented `2^61` ceiling.

`from_f64_dir` is now a two-line composition of `f64_decompose` with that core,
and still ensures only `wf()` — correctly, since no postcondition mentioning `v`
is statable at all. The boundary is now visible in the type signatures instead of
being described in this file.

**Tests backing it.**

| test | what it pins |
|---|---|
| `oracle::from_f64_matches_oracle` | R3 against `malachite_q::Rational::try_from(f64)` — the oracle's own independent IEEE-754 decoding — over 5,000 random doubles plus 17 hand-picked specials, in all three directions; plus R2 for `Down`/`Up`, plus rejection of NaN and both infinities |
| `adversarial::f64_boundary_edges` | exact round-trip of every power of two from `2^-60` to `2^61`; `±0.0`; the smallest subnormal `5e-324`; values below the finest grid; magnitude rejection at `2^62` and `f64::MAX`; and that `0.1_f64` converts to the *double*, not to `1/10` |

If the decomposition were wrong in any bit position, `from_f64_matches_oracle`
would fail immediately: the oracle decodes the same float independently and to
arbitrary precision.

---

## 2. `convert::to_f64`

```rust
#[verifier::external_body]
pub fn to_f64(q: Q) -> f64 {
    (q.num as f64) / (q.den as f64)
}
```

**Why it is trusted.** Proving floating-point rounding inside Verus is a
substantial project on its own, and this function's entire job is to hand a
number to a JSON encoder or a log line. The specification explicitly designates
it as the one documented trusted output boundary.

**What is assumed.** Nothing about the result is stated in an `ensures` clause,
so verified code learns nothing from calling it — which is the correct outcome,
because verified code should never call it. The only assumption is the one made
by users: that the returned `f64` is close to `q`.

**Accuracy.** Three roundings happen (numerator to `f64`, denominator to `f64`,
then the division), so the relative error is at most about `3 · 2^-53`.

**Tests backing it.** `oracle::to_f64_is_within_four_ulp` converts 20,000 random
`Q` values, decodes the resulting `f64` back to an exact `Rational` with the
oracle, and asserts the relative error is within 4 ulp.

**Do not feed the output back into `Q`.** `to_f64` is a lossy projection.
Round-tripping through it silently reintroduces every `f64` problem this crate
exists to remove — non-associativity, order dependence, and unprovable error.
Use `serde` (which encodes the exact `(num, den)` pair) or `Display` for
anything that has to come back.

---

## Not trusted, but outside the verified region

The standard-library trait implementations are marked
`#[cfg_attr(verus_keep_ghost, verifier::external)]`, which is a *different*
thing from `external_body`: Verus ignores them entirely and verified code cannot
call them, so they contribute no assumptions to any proof. They exist for
ergonomics at the crate boundary.

| item | body |
|---|---|
| `impl Ord for Q` | delegates to the verified `Q::compare`, mapping its `-1`/`0`/`1` onto `Ordering` |
| `impl PartialOrd for Q` | delegates to `impl Ord for Q` |
| `impl Add/Sub/Mul/Neg for Q` | delegate to `Q::add`/`Q::sub`/`Q::mul`/`Q::neg` |
| `impl Display for Q` | `write!(f, "{}/{}", num, den)` |
| `impl Serialize/Deserialize for Q` (feature `serde`) | encode the `(num, den)` pair; decode through the verified `Q::new`, so a hand-written or corrupted payload yields an error rather than a value violating the type invariant |

`Div` is deliberately **not** implemented: division carries a precondition
(`!b.is_zero()`) that an operator cannot express. Callers use `Q::div`, and
under Verus they discharge the precondition statically.

These are exercised by the same test suite as everything else —
`props::ord_is_a_total_order_agreeing_with_the_value_order`,
`props::hash_agrees_with_eq`, `props::display_is_canonical`,
`props::serde_round_trips_exactly`, and the `cmp` assertions in
`oracle::exhaustive_small_rationals`.
