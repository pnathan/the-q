# Trusted boundary

Everything in `the-q` is verified integer arithmetic **except** the three
functions below. Each is marked `#[verifier::external_body]`, which means Verus
takes its `ensures` clause on faith and never looks at the body. Each is listed
here with the specification that is being assumed and the tests that check the
assumption against reality.

Another float function, `convert::q_from_f64`, sits outside the verified region
but is *not* `external_body` and assumes nothing numeric — see the section at
the end.

There are no `assume(...)` or `admit()` calls anywhere in the shipping code.
Grep for them: `rg 'assume\(|admit\(' src/` returns nothing.

Two of the three sit at the crate's `f64` edge. Neither is on any arithmetic
path — `Rat + Rat`, `Rat * Rat`, comparison, canonicalisation and rounding never
touch a float. The same holds for the extended `Q`: none of
`Q::add`/`sub`/`mul`/`div`/`recip`, the order, or the predicates touches a
float.

The third, `q::require_nonzero`, computes nothing. It is a runtime check that
either returns or panics, and it is trusted for its panic message rather than
for any numeric claim.

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

Those hold for the domain the `requires` names — `mant <= 2^53` and
`-1074 <= e <= 971`, exactly what `f64_decompose` can emit. A `requires` is
ghost, though, and this function is `pub`, so it binds only callers Verus
checks; an unverified one passing a larger `mant` would reach `mant · 2^e` and
overflow `i128`. The body re-checks the same bounds at run time and returns
`None` outside them, so the function is total for every caller, not just the
provable ones. That check is dead code under verification, which is why none of
the postconditions above are weakened by it.

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
pub fn to_f64(q: Rat) -> f64 {
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
`Rat` values, decodes the resulting `f64` back to an exact `Rational` with the
oracle, and asserts the relative error is within 4 ulp.

**Do not feed the output back into `Rat`.** `to_f64` is a lossy projection.
Round-tripping through it silently reintroduces every `f64` problem this crate
exists to remove — non-associativity, order dependence, and unprovable error.
Use `serde` (which encodes the exact `(num, den)` pair) or `Display` for
anything that has to come back.

---

## 3. `q::require_nonzero`

```rust
#[verifier::external_body]
pub fn require_nonzero(nonzero: bool, msg: &str)
    requires
        nonzero,
{
    assert!(nonzero, "{}", msg);
}
```

**Why it is trusted.** For its message, and for nothing else. `Rat::div_dir` and
`Rat::recip` carry `n() != 0` as a precondition; verified code discharges it, so
this call is a branch that is never taken and the body is unreachable. Unverified
code cannot discharge a precondition, and this check is what turns that case into
a panic that names the operation and the alternative, rather than
`attempt to divide by zero` from inside `round_frac_exec` or a returned
`Rat { num: -1, den: 0 }`.

`vstd::pervasive::runtime_assert` has the identical contract and would need no
trusted code here. It panics with `assertion failed: b` at a line inside `vstd`,
which names neither the operation nor the fix. The trade is one trusted function
against an error message a caller can act on.

**What is assumed.** That the function returns when `nonzero` is true, and does
not return when it is false. Nothing numeric. The `requires` clause is what
Verus checks at each call site, and the two call sites discharge it from the
operation's own precondition.

**What is not assumed.** Anything about the values being divided. The function
takes a `bool` and a `&str`, performs no arithmetic, and returns nothing. It
cannot alter a result; it can only stop a call.

**Tests backing it.** `adversarial::div_by_zero_panics` and
`adversarial::recip_of_zero_panics` check the panic. `extended_q::the_motivating_defects_are_fixed`
checks it against the `Q` behaviour for the same inputs.

---

## Not trusted, but outside the verified region

The standard-library trait implementations are marked
`#[cfg_attr(verus_keep_ghost, verifier::external)]`, which is a *different*
thing from `external_body`: Verus ignores them entirely and verified code cannot
call them, so they contribute no assumptions to any proof. They exist for
ergonomics at the crate boundary.

| item | body |
|---|---|
| `impl Ord for Rat` | delegates to the verified `Rat::compare`, mapping its `-1`/`0`/`1` onto `Ordering` |
| `impl PartialOrd for Rat` | delegates to `impl Ord for Rat` |
| `impl Add/Sub/Mul/Neg for Rat` | delegate to `Rat::add`/`Rat::sub`/`Rat::mul`/`Rat::neg` |
| `impl Display for Rat` | `write!(f, "{}/{}", num, den)` |
| `impl Serialize/Deserialize for Rat` (feature `serde`) | encode the `(num, den)` pair; decode through the verified `Rat::new`, so a hand-written or corrupted payload yields an error rather than a value violating the type invariant |
| `impl Ord for Q` | delegates to the verified `Q::compare`, which is proven total, antisymmetric and transitive against the ghost order |
| `impl PartialOrd for Q` | delegates to `impl Ord for Q` |
| `impl Display for Q` | `num/den` for a number; the fixed spellings `nan`, `inf`, `-inf`, `>max`, `<-max` for the specials |
| `impl FromStr for Q` | parses exactly what `Display` emits, plus a bare integer; rejects whitespace, a zero denominator, and out-of-budget values with distinct errors |
| `impl Serialize/Deserialize for Q` (feature `serde`) | untagged: the `(num, den)` pair for a number, the `Display` spelling for a special. Decoding goes through the verified `Rat::new`. Uses `deserialize_any`, so it works only in **self-describing** formats — `bincode` and similar will fail at runtime |
| `impl Add/Sub/Mul/Div/Neg for Q` | delegate to `Q::add`/`sub`/`mul`/`div`/`neg`. **`Div` exists here and not on `Rat`**: the reason `Rat` omits it is that its division carries a precondition (`!b.is_zero()`) an operator cannot express, and `Q::div` is total, so there is no input for which `a / b` fails to produce a value |
| `impl Default for Q` | `Q::zero()` |
| `convert::q_from_f64` | total `f64 → Q`. Splits on `is_nan`/`is_infinite`/`is_sign_negative` and delegates the value path to `from_f64_dir`. Adds no numeric assumption beyond `f64_decompose`'s: all it contributes is a three-way split on classes IEEE-754 defines unambiguously |

`Q`'s arithmetic — `add`, `sub`, `mul`, `div`, `recip`, `pow_u32`, the four
`checked_*`, the predicates, the order, and `min`/`max`/`clamp` — is **inside**
the verified region and contributes no assumptions. What the enum layer does
not carry is a ghost restatement of the propagation tables in #26 §5; those are
pinned by exhaustive enumeration of the 6×6 state space in
`tests/extended_q.rs` rather than by proof, deliberately, because a
specification shaped exactly like the table it specifies would verify with a
mistake duplicated into both.

`Div` is deliberately **not** implemented **for `Rat`**: division there carries
a precondition (`!b.is_zero()`) that an operator cannot express. Callers use
`Rat::div`, and under Verus they discharge the precondition statically. On the
extended `Q` that precondition is gone — `Q::div` is total — so the objection no
longer applies to that type.

These are exercised by the same test suite as everything else —
`props::ord_is_a_total_order_agreeing_with_the_value_order`,
`props::hash_agrees_with_eq`, `props::display_is_canonical`,
`props::serde_round_trips_exactly`, and the `cmp` assertions in
`oracle::exhaustive_small_rationals`.
