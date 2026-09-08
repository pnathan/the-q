# the-q

[![CI](https://github.com/pnathan/the-q/actions/workflows/ci.yml/badge.svg)](https://github.com/pnathan/the-q/actions/workflows/ci.yml)
[![crates.io](https://img.shields.io/crates/v/the-q.svg)](https://crates.io/crates/the-q)
[![docs.rs](https://img.shields.io/docsrs/the-q)](https://docs.rs/the-q)
[![licence](https://img.shields.io/badge/licence-AGPL--3.0--or--later-blue.svg)](#licence)

Bounded rational arithmetic for Rust, with a rounding contract that is
machine-checked in [Verus](https://github.com/verus-lang/verus).

A value is two `i64` words. Arithmetic is exact whenever the exact result fits
that budget, and when it does not, the result is rounded to a proven error
bound in a direction you choose. Nothing overflows, nothing allocates, and
every operation on the total type `Q` returns a value, never a panic.

```rust
use the_q::{Q, Rat};

let price = Rat::from_decimal(1999, 2).unwrap(); // 19.99, exactly
let rate = Rat::from_decimal(825, 4).unwrap(); //  0.0825, exactly
let tax = Rat::mul(price, rate); //  1.649175, exactly
assert_eq!(tax.to_string(), "65967/40000");

let third = Rat::new(1, 3).unwrap();
assert_eq!(third + third + third, Rat::one()); // no drift

// Division by zero is not a panic on `Q`; it is a value.
assert_eq!(Q::new(1, 0), Q::PosInf);
assert_eq!(Q::div(Q::zero(), Q::zero()), Q::Nan);
```

## Why

Every representation of a real number in a machine makes a compromise, and
the usual ones make it silently.

* **`f64`** rounds on almost every operation, to a bound that is relative, so
  `0.1 + 0.2 != 0.3` and a long sum drifts by an amount no one has written
  down.
* **`Ratio<i64>`** is exact until the moment it overflows, and then it panics,
  or wraps, depending on the build profile.
* **Arbitrary-precision rationals** are exact forever, and their denominators
  grow without bound: a chain of a few thousand operations holds megabytes and
  each step gets slower than the last.

`the-q` takes the fourth position. A `Rat` is a canonical fraction whose
numerator and denominator are each bounded by `2^62 − 1`, chosen so that every
cross-multiplied `i128` intermediate provably fits. When an exact result would
leave that budget, it is rounded, once, to a dyadic grid, and the rounding
satisfies four properties (R1–R4 below) that are theorems about the code, not
documentation of it. A step rounds only when its reduced result no longer fits
`2^62 − 1`: sums and products of a handful of small fractions are exact, while
in a long chain the denominators grow until every step rounds, each time by a
proven amount, in the direction you asked for.

The proofs are written in Verus inside the source files. `cargo build` erases
them and compiles ordinary Rust; `cargo verus verify` checks them. The verified
count in CI is `1219 verified, 0 errors`, with no `assume`, no `admit`, and
three trusted functions, all at the `f64` boundary or a panic message, none on
an arithmetic path.

This is the right tool when memory must be flat, chains are long or unbounded,
results must be bit-identical across machines, or the per-step error must be a
proven number. For short exact computations use an exact rational; for raw
speed use `f64`.

## Install

```toml
[dependencies]
the-q = "0.2.1"

# Optional features, all off by default:
# the-q = { version = "0.2.1", features = ["serde", "rust_decimal"] }
```

| feature | adds |
|---|---|
| `serde` | `Serialize`/`Deserialize` for `Rat` and `Q` |
| `rust_decimal` | conversions from `rust_decimal::Decimal` |
| `fixed` | conversions from every 128-bit `fixed` type |
| `num-rational` | conversions from `Ratio<i64>` and `BigRational` |
| `num-bigint` | conversions from `BigInt` |
| `bigdecimal` | conversions from `BigDecimal` |
| `all-integrations` | the five library conversions at once |

MSRV is Rust 1.85, edition 2024. Verus is not needed to build or use the
crate; it is needed only to re-check the proofs.

## The types

| type | what it is | failure mode |
|---|---|---|
| [`Rat`](#rat) | a canonical bounded fraction, `Copy`, 128 bits | partial: `None` on a bad constructor argument, panic on a zero divisor, saturation on overflow |
| [`Q`](#q) | `Rat` plus explicit `±Sat`, `±Inf`, `Nan` | total: every operation returns a `Q` |
| [`QI`](#qi) | an interval `[lo, hi]` of `Rat` with proven enclosure | panic on `lo > hi` in `new`; `checked_new` |
| [`Exact`](#exact) | a `Rat` whose operations refuse to round | `Result<Exact, ExactError>` |
| `Dir` | `Down`, `Up`, `Nearest`: the rounding direction | |
| `Sign` | `Negative`, `Zero`, `Positive`: what `Q::signum` returns | |
| `ExactError`, `ParseQError` | the error enums of `Exact` and `Q: FromStr` | |
| `MAX_MAG`, `MAX_DEC_PLACES` | `2^62 − 1`, and `18`, the largest decimal exponent `from_decimal` accepts | |
| `MAX_DECIMAL_SCALE`, `MAX_DECIMAL_MANTISSA` | `28` and `2^96 − 1`: the domain of a `rust_decimal::Decimal`, which `from_decimal128_dir` accepts in full | |

Plus the module [`nary`](#n-ary-folds) (reproducible folds over `Rat`), the
[roots and transcendentals](#roots-and-transcendentals) on `Q`, and the
[conversions](#conversions-and-serialisation): `from_f64_dir`, `q_from_f64`,
`to_f64`, the `i128` cores `from_decimal128_*` and `from_ratio128_*`, the
feature-gated library adapters, `Display`, `FromStr` and serde.

Everything named in this section follows semver. Modules such as `gcd`,
`model`, `round`, `lipschitz`, `fx`, `denote`, `laws_q`, `soundness*` and
helpers such as `q::add_n_exec` are public only because Verus's visibility
rules demand it, and may change shape in a patch release.

## `Rat`

`Rat` is `num / den` in two private `i64` fields. It is always canonical
(`den > 0`, `gcd(|num|, den) == 1`, and `0` is `0/1`) and always bounded
(`|num|, den ≤ 2^62 − 1`). Because the fields are private, every `Rat` a
caller can hold came from a constructor and satisfies the invariant, and
because the form is canonical, the derived `Eq` and `Hash` are value equality.
It is `Copy`, `Send + Sync`, and does not touch the heap.

### Constructing

```rust
use the_q::{Dir, MAX_DEC_PLACES, MAX_MAG, Rat};

// Every constructor canonicalises: sign on the numerator, gcd removed.
assert_eq!(Rat::new(6, 8), Rat::new(3, 4));
assert_eq!(Rat::new(3, -6).unwrap().to_string(), "-1/2");
assert_eq!(Rat::new(0, -7), Some(Rat::zero()));

// `None` for a zero denominator, or a pair that does not fit the budget.
assert_eq!(Rat::new(1, 0), None);
assert_eq!(Rat::new(i64::MAX, 1), None);

// Decimal literals are exact; `(1999, 2)` is 19.99.
assert_eq!(Rat::from_decimal(1999, 2).unwrap().to_string(), "1999/100");
assert_eq!(Rat::from_decimal(1, MAX_DEC_PLACES + 1), None);

// `new_rounded` is total in the numerator: it rounds instead of refusing.
let big = Rat::new_rounded(i64::MAX, 1, Dir::Down).unwrap();
assert_eq!(big.numerator(), MAX_MAG);
assert_eq!(Rat::new_rounded(1, 0, Dir::Down), None);

assert_eq!(Rat::from_int(-5).unwrap(), Rat::new(-5, 1).unwrap());
```

### Arithmetic

The plain operations round to nearest, ties to even. The `*_dir` variants take
a `Dir`. The `checked_*` variants return `None` when the result saturates (and
`checked_div` also when the divisor is zero). `neg`, `abs`, `recip`, `min`,
`max` and `clamp` are exact. `pow_u32` is a fold of `mul`.

```rust
use the_q::Rat;

let a = Rat::new(1, 3).unwrap();
let b = Rat::new(1, 6).unwrap();

// Exact when the exact result fits, which is nearly always.
assert_eq!(Rat::add(a, b), Rat::new(1, 2).unwrap());
assert_eq!(a + b, Rat::new(1, 2).unwrap()); // operators delegate
assert_eq!(a - b, Rat::new(1, 6).unwrap());
assert_eq!(a * b, Rat::new(1, 18).unwrap());
assert_eq!(-a, Rat::new(-1, 3).unwrap());
assert_eq!(Rat::div(a, b), Rat::new(2, 1).unwrap());

// No `/` operator on `Rat`: `div` has a precondition the operator cannot
// express. Use `Rat::div`, `Rat::checked_div`, or move to `Q`.
assert_eq!(Rat::checked_div(a, Rat::zero()), None);

assert_eq!(a.recip(), Rat::new(3, 1).unwrap());
assert_eq!(a.pow_u32(3), Rat::new(1, 27).unwrap());
assert_eq!(Rat::new(-2, 5).unwrap().abs(), Rat::new(2, 5).unwrap());
```

### When rounding happens

Most sums and products of everyday fractions are exact. Rounding occurs only
when the reduced result has a numerator or denominator above `2^62 − 1`. Here
is one that does:

```rust
use the_q::{Dir, MAX_MAG, Rat};

// Reduced denominator of the sum is about 9.2e18, past the 2^62 budget.
let a = Rat::new(1, 3_037_000_493).unwrap();
let b = Rat::new(1, 3_037_000_499).unwrap();

let nearest = Rat::add(a, b); // rounded, ties to even
let down = Rat::add_dir(a, b, Dir::Down);
let up = Rat::add_dir(a, b, Dir::Up);
assert!(down <= nearest && nearest <= up); // R2: the exact sum lies in [down, up]
assert!(down < up); // so rounding did happen

// `checked_*` on `Rat` reports saturation only, not rounding.
assert!(Rat::checked_add(a, b).is_some());
let m = Rat::new(MAX_MAG, 1).unwrap();
assert_eq!(Rat::checked_add(m, m), None); // over the budget
assert_eq!(Rat::add(m, m), m); // the plain op saturates
```

`Rat` is deliberately **partial**: `Rat::new(_, 0)` is `None`; `Rat::div(x, 0)`
and `Rat::zero().recip()` panic (a precondition under Verus, a runtime check
with a message for everyone else); an exact result above the budget saturates
to `±(2^62 − 1)`, which the `checked_*` variants report as `None` and the
plain operations do not. `Q` turns each of those into a value.

### Comparing

```rust
use std::collections::BTreeMap;
use the_q::Rat;

let a = Rat::new(1, 3).unwrap();
let b = Rat::new(1, 2).unwrap();

// Exact and total: cross-multiplication, never a float.
assert!(a < b);
assert_eq!(Rat::compare(a, b), -1);
assert_eq!(Rat::min(a, b), a);
assert_eq!(Rat::clamp(Rat::new(7, 1).unwrap(), a, b), b);

// `Eq` and `Hash` are structural, and canonical form makes that value
// equality, so `Rat` is a map key.
let mut table = BTreeMap::new();
table.insert(Rat::new(2, 4).unwrap(), "half");
assert_eq!(table.get(&b), Some(&"half"));

assert_eq!(Rat::new(-3, 4).unwrap().signum(), -1);
assert!(Rat::new(3, 4).unwrap().in_unit_interval());
assert!(Rat::zero().is_zero() && Rat::one().is_one());
```

### Reading it out

```rust
use the_q::{Rat, to_f64};

let x = Rat::new(1, 3).unwrap();
assert_eq!(x.to_string(), "1/3"); // always `num/den`, always canonical
assert_eq!(x.numerator(), 1);
assert_eq!(x.denominator(), 3);
assert!((to_f64(x) - 0.333_333_333_333_333_3).abs() < 1e-15); // display only
```

## `Q`

`Q` is the total layer. It is a wrapper around `Rat`, not a rewrite: the
kernel's invariant and proofs are untouched, and `Q` adds five payload-free
states for the values a `Rat` cannot hold.

```rust,ignore
pub enum Q {
    Number(Rat),
    PosSat, NegSat,   // a finite real whose magnitude exceeds the budget
    PosInf, NegInf,   // exactly infinite
    Nan,              // no information
}
```

Every operation on `Q`, including arithmetic, comparison, the folds, and every
root and transcendental, returns a `Q` and never panics.

```rust
use the_q::{MAX_MAG, Q, Rat};

// Every `Rat` failure mode is a `Q` value.
assert_eq!(Q::new(1, 0), Q::PosInf);
assert_eq!(Q::new(-1, 0), Q::NegInf);
assert_eq!(Q::new(0, 0), Q::Nan);
assert_eq!(Q::new(6, 8), Q::Number(Rat::new(3, 4).unwrap()));

assert_eq!(Q::div(Q::one(), Q::zero()), Q::PosInf);
assert_eq!(Q::one() / Q::zero(), Q::PosInf); // `Q` has a `/` operator
assert_eq!(Q::zero().recip(), Q::PosInf);

// Overflow is reported as saturation, distinct from infinity.
let m = Q::Number(Rat::new(MAX_MAG, 1).unwrap());
let over = m + m;
assert_eq!(over, Q::PosSat);
assert!(over.is_saturated() && !over.is_infinite());
assert_eq!(over.to_string(), ">max");

// `checked_*` on `Q` returns `Option<Rat>`: `Some` only for a number.
assert_eq!(Q::checked_add(m, m), None);
assert_eq!(Q::checked_div(Q::one(), Q::zero()), None);
assert_eq!(Q::checked_mul(Q::one(), Q::one()), Some(Rat::one()));
```

Three choices differ deliberately from IEEE 754, and each is proven:

* **Saturation is finite.** `PosSat` denotes the reals above `2^62 − 1`, not
  infinity. So `0 * PosSat == 0`, and there is no `is_finite()`, because a
  saturated value *is* finite.
* **The order is total.** `Nan == Nan`, and `Nan` sorts last, so `Q` is `Eq`,
  `Hash`, `Ord`, and a valid map key. Outside `Number` the order is on
  representations, not values.
* **Selection propagates `Nan`.** `Q::min`, `Q::max` and `Q::clamp` return
  `Nan` if either input is `Nan`. `Ord::min` cannot do that, so a fold of
  `Q::min` is not `iter().min()`.

```rust
use the_q::{Q, Sign};

// Saturation denotes a finite real, so this is exact where `0 * inf` is not.
assert_eq!(Q::mul(Q::zero(), Q::PosSat), Q::zero());
assert_eq!(Q::mul(Q::zero(), Q::PosInf), Q::Nan);
assert_eq!(Q::PosInf - Q::PosInf, Q::Nan);
assert_eq!(Q::PosSat.abs(), Q::PosSat);
assert_eq!(-Q::NegSat, Q::PosSat);

// The order is total and `Nan == Nan`, so `Q` is a map key too.
let mut v = vec![Q::Nan, Q::PosInf, Q::zero(), Q::NegSat, Q::NegInf];
v.sort();
assert_eq!(v, vec![Q::NegInf, Q::NegSat, Q::zero(), Q::PosInf, Q::Nan]);

// Selection propagates `Nan`; `Ord::min` cannot, so do not fold with it.
assert_eq!(Q::min(Q::Nan, Q::one()), Q::Nan);
assert_eq!([Q::Nan, Q::one()].into_iter().min(), Some(Q::one()));

// Every non-`Nan` value has a sign.
assert_eq!(Q::PosSat.signum(), Some(Sign::Positive));
assert_eq!(Q::zero().signum(), Some(Sign::Zero));
assert_eq!(Q::Nan.signum(), None);
```

### Folds

`Q::sum`, `Q::product` and `Q::weighted_mean` are fixed left folds. The order
is part of the contract: with rounding, addition is not associative, so fixing
the order is what makes the result bit-identical across machines and threads.

```rust
use the_q::Q;

let third = Q::new(1, 3);
assert_eq!(Q::sum(&[third, third, third]), Q::one());
assert_eq!(Q::product(&[Q::new(2, 1), Q::new(1, 4)]), Q::new(1, 2));

// `(weight, value)` pairs. Total: a zero weight sum is `Nan` or `±Inf`.
let mean = Q::weighted_mean(&[(Q::new(1, 2), Q::one()), (Q::new(1, 2), Q::zero())]);
assert_eq!(mean, Q::new(1, 2));
assert_eq!(Q::weighted_mean(&[]), Q::Nan);

// A `Nan` anywhere in the fold is a `Nan` result.
assert_eq!(Q::sum(&[Q::one(), Q::Nan]), Q::Nan);
```

### Text

```rust
use std::str::FromStr;
use the_q::{ParseQError, Q};

// `Display` and `FromStr` round-trip every state.
for q in [
    Q::new(-3, 4),
    Q::PosSat,
    Q::NegSat,
    Q::PosInf,
    Q::NegInf,
    Q::Nan,
] {
    assert_eq!(Q::from_str(&q.to_string()), Ok(q));
}
assert_eq!(Q::Nan.to_string(), "nan");
assert_eq!(Q::NegSat.to_string(), "<-max");

// Input is canonicalised; a bare integer is accepted; a zero denominator
// in *text* is a malformed numeral, not a computation.
assert_eq!("2/4".parse::<Q>(), Ok(Q::new(1, 2)));
assert_eq!("7".parse::<Q>(), Ok(Q::new(7, 1)));
assert_eq!("1/0".parse::<Q>(), Err(ParseQError::ZeroDenominator));
assert_eq!("0.5".parse::<Q>(), Err(ParseQError::Malformed));
```

### Which laws survive

`Q::add` and `Q::mul` are commutative for every input. Associativity,
distributivity and monotonicity hold only while every operand and every
intermediate is a `Number` on the exact path; that is the same scope as
`Rat`'s laws, not a wider one. Once a saturation is reachable all three fail,
and `Q::div(a, b)` differs from `Q::mul(a, Q::recip(b))` in the six cells
`{NegInf, PosInf, Number(0)} × {PosSat, NegSat}`. Each failure has an
executable counterexample in `tests/q_laws.rs`; the proofs (V11 below) cover
the laws where they hold, and, separately, that every special-value cell of
the propagation tables contains the true result.

```rust
use the_q::{MAX_MAG, Q, Rat};

let m = Q::Number(Rat::new(MAX_MAG, 1).unwrap());
let neg_m = Q::Number(Rat::new(-MAX_MAG, 1).unwrap());

// Commutative always.
assert_eq!(Q::add(m, neg_m), Q::add(neg_m, m));

// Associative only while no operand saturates: (m + m) + (-m) hits `PosSat`
// first and `PosSat + NegSat` is indeterminate, but m + (m + -m) is exact.
assert_eq!(Q::add(Q::add(m, m), neg_m), Q::Nan);
assert_eq!(Q::add(m, Q::add(m, neg_m)), m);

// `div` is not `mul` by `recip` once saturation is involved.
assert_eq!(Q::div(Q::zero(), Q::PosSat), Q::zero());
assert_eq!(Q::mul(Q::zero(), Q::PosSat.recip()), Q::Nan);
```

## `QI`

`QI` is a closed interval `[lo, hi]` of `Rat`. Its lower endpoint is always
computed with `Dir::Down` and its upper with `Dir::Up`, so enclosure follows
from R2 with no new rounding proofs. It is proven for `add`, `sub`, `neg` and
`mul` across every sign pattern.

```rust
use the_q::{MAX_MAG, Q, QI, Rat};

let a = QI::new(Rat::new(1, 3).unwrap(), Rat::new(1, 2).unwrap()); // [1/3, 1/2]
let b = QI::exact(Rat::new(3, 1).unwrap()); // [3, 3]

// Endpoints round outward (`lo` down, `hi` up), so enclosure is proven:
// if `x ∈ a` and `y ∈ b` then `x ∘ y ∈ a ∘ b` for `+`, `-`, `*`.
let s = QI::add(a, b);
assert_eq!(s.lower(), Rat::new(10, 3).unwrap());
assert_eq!(s.upper(), Rat::new(7, 2).unwrap());
assert!(s.contains(Rat::add(Rat::new(2, 5).unwrap(), Rat::new(3, 1).unwrap())));

let p = QI::mul(a, QI::neg(b)); // sign patterns are all handled
assert_eq!(p.lower(), Rat::new(-3, 2).unwrap());
assert_eq!(p.upper(), Rat::new(-1, 1).unwrap());

// `width` is rounded up and returned as a `Q`: `PosSat` if too wide.
assert_eq!(a.width(), Q::new(1, 6));
assert_eq!(a.checked_width(), Some(Rat::new(1, 6).unwrap()));
let whole = QI::new(
    Rat::new(-MAX_MAG, 1).unwrap(),
    Rat::new(MAX_MAG, 1).unwrap(),
);
assert_eq!(whole.width(), Q::PosSat);
assert_eq!(whole.checked_width(), None);

// `hull` is the smallest interval containing both.
assert_eq!(
    QI::hull(a, b),
    QI::new(Rat::new(1, 3).unwrap(), Rat::new(3, 1).unwrap())
);

// `lo > hi` is a precondition: `new` panics, `checked_new` is `None`.
assert_eq!(QI::checked_new(Rat::one(), Rat::zero()), None);
```

## `Exact`

`Exact` is a `Rat` wrapper for callers who would rather fail than round. Its
`add`, `sub`, `mul` and `div` succeed only when the result needs no rounding,
and return `Result<Exact, ExactError>` (`Inexact`, or `DivisionByZero` for
`div`) the moment they would leave the exact path. The `checked_*` variants
return `Option` instead.

The difference from `Rat::checked_*` matters: `Rat::checked_add` is `None`
only on saturation, and silently rounds otherwise. `Exact::checked_add` is
`None` on *any* rounding.

```rust
use the_q::{Exact, ExactError, Rat};

let half = Exact::new(Rat::new(1, 2).unwrap());
assert_eq!(Exact::add(half, half).unwrap().value(), Rat::one());
assert_eq!(
    Exact::mul(half, half).unwrap().value(),
    Rat::new(1, 4).unwrap()
);

// The same two operands `Rat::add` rounds above: here they are an error.
let a = Exact::new(Rat::new(1, 3_037_000_493).unwrap());
let b = Exact::new(Rat::new(1, 3_037_000_499).unwrap());
assert_eq!(Exact::add(a, b), Err(ExactError::Inexact));
assert_eq!(Exact::checked_add(a, b), None);
assert!(Rat::checked_add(a.value(), b.value()).is_some()); // `Rat` only refuses saturation

// Division by zero is a separate error, not a panic.
assert_eq!(
    Exact::div(half, Exact::new(Rat::zero())),
    Err(ExactError::DivisionByZero)
);
assert_eq!(Exact::checked_div(half, Exact::new(Rat::zero())), None);

// `Exact` has no `Ord`; compare with `Exact::le`.
assert!(Exact::le(half, Exact::new(Rat::one())));
assert!(half.is_nonneg());
```

What you buy with the refusal: associativity, distributivity and monotonicity,
absent in general once rounding happens (see [Limits](#limits)), hold for any
chain of `Exact` operations in which every step succeeded. That is sufficient,
not claimed necessary, and it is proven (`theorem_exact_add_associative`,
`theorem_exact_mul_associative`, `theorem_exact_distributive`,
`theorem_exact_add_monotone`, `theorem_exact_mul_monotone_nonneg`).

## Roots and transcendentals

`sqrt`, `cbrt`, `hypot`; `exp`, `exp2`, `powf`, `pow_i32`, `ln`, `log2`,
`log10`, `log`; `sin`, `cos`, `tan`, `asin`, `acos`, `atan`, `atan2`; `sinh`,
`cosh`, `tanh`; and the constants `pi`, `e`, `ln2`, `ln10`, `half_pi` in the
`transcendental` module. They live on `Q` because none of them is
rational-closed. All are total, and all are fixed-length series, so termination
is structural and cost is constant.

```rust
use the_q::transcendental;
use the_q::{Q, Rat, to_f64};

// Exact where the answer is rational.
assert_eq!(Q::new(4, 1).sqrt(), Q::new(2, 1));
assert_eq!(Q::new(9, 4).sqrt(), Q::new(3, 2));
assert_eq!(Q::zero().exp(), Q::one());
assert_eq!(Q::one().ln(), Q::zero());
assert_eq!(Q::new(2, 1).pow_i32(-3), Q::new(1, 8)); // a fold of `mul`

// Otherwise a bounded rational near the true value; accuracy is measured,
// not proven (see the table below).
let Q::Number(pi) = transcendental::pi() else {
    panic!()
};
assert!((to_f64(pi) - std::f64::consts::PI).abs() < 1e-15);
let Q::Number(e) = Q::one().exp() else {
    panic!()
};
assert!((to_f64(e) - std::f64::consts::E).abs() < 1e-15);
// `cbrt(8)` goes through `exp(ln)` and is a hair off 2, not 2. The
// logarithms at powers of their base are exact by a proven postcondition.
let Q::Number(two) = Q::new(8, 1).cbrt() else {
    panic!()
};
assert_ne!(two, Rat::new(2, 1).unwrap());
assert!((to_f64(two) - 2.0).abs() < 1e-15);
assert_eq!(Q::new(8, 1).log2(), Q::new(3, 1));
assert_eq!(Q::new(1, 1000).log10(), Q::new(-3, 1));

// Total: every domain edge is a value, never a panic.
assert_eq!(Q::new(-1, 1).sqrt(), Q::Nan);
assert_eq!(Q::zero().ln(), Q::NegInf);
assert_eq!(Q::new(50, 1).exp(), Q::PosSat); // above the budget
assert_eq!(Q::new(-50, 1).exp(), Q::zero()); // below the grid
assert_eq!(Q::PosSat.sqrt(), Q::Nan); // the image reaches back inside
assert_eq!(Q::PosInf.atan(), transcendental::half_pi());
assert_eq!(Q::Nan.sin(), Q::Nan);
```

Domains: `exp` returns `PosSat` above `x = 43.67` and `0` below `−44`; `sin`,
`cos`, `tan` return `Nan` for `|x| > 2^20`; `sqrt(PosSat)` and `ln(PosSat)` are
`Nan` because the image of the saturated region reaches back inside the budget.

**Accuracy is measured, not proven.** Totality and termination are theorems;
the error figures are observations. Two independent oracles were used, mpmath
at 120 decimal digits and exact rational series in Common Lisp carried to
`2^-160`, and they agree with each other to better than `2^-98` on every
function. Worst observed error over the sweeps (`tests/transcendental.rs` and
`scripts/accuracy/`), in R3's own metric `|got − true| / max(1, |true|)`:

| function | worst error | note |
|---|---|---|
| `exp`, `cosh`, `sinh`, `tanh` | `2^-61` | |
| `e` | `2^-63` | |
| `sqrt` | `2^-61` | |
| `hypot` | `2^-62` | |
| `cbrt`, `powf` | `2^-60` | via `exp(ln)` |
| `pi`, `ln2`, `atan2` | `2^-60` | |
| `ln`, `log2` | `2^-59` | |
| `log10` | `2^-61` | |
| `atan`, `asin`, `acos` | `2^-58` | |
| `sin`, `cos`, `tan` | `2^-59` at `\|x\| ≤ 1`, `2^-57` at `≤ 8`, `2^-50` at `≤ 2^10`, `2^-40` at `≤ 2^20` | reduction error grows as `\|x\| · 2^-60` |
| `exp2` | `\|x\| · 2^-61` (`2^-55` at `x = 40`) | argument scaled by a rounded `ln 2` |

Read the table with the R3 caveat below: these are absolute bounds below 1.
`asin(0.002)` is `2^-53` *relative*; `exp(−40)` is `2^-3`; `exp(−44)` is `0`.
`tan` near a pole inherits `cos`'s absolute error divided by `cos²`, so it is
unbounded there. `ln` within `2^-8` of 1 keeps a small-denominator rational and
is often far better than `2^-61` absolute, but not uniformly: `2^-52` relative
at `1 ± 2^-24`, `2^-124` at `1 ± 2^-60`.

`pi`, `e`, `ln2`, `ln10` are literals; each has a `*_series` derivation and a
test that the two are bit-identical.

## N-ary folds

The `nary` module has the same three folds as `Q` for callers who stay on
`Rat`. `sum` and `product` are total. `weighted_mean` takes `(weight, value)`
pairs and is `None` when the rounded weight sum is zero, whether the weights
cancel or their sum is below the grid.

```rust
use the_q::Rat;
use the_q::nary;

let third = Rat::new(1, 3).unwrap();
assert_eq!(nary::sum(&[third, third, third]), Rat::one());
assert_eq!(nary::sum(&[]), Rat::zero());
assert_eq!(
    nary::product(&[Rat::new(2, 3).unwrap(), Rat::new(3, 4).unwrap()]),
    Rat::new(1, 2).unwrap()
);

// `(weight, value)` pairs; `None` when the rounded weight sum is zero.
let pairs = [
    (Rat::new(1, 4).unwrap(), Rat::one()),
    (Rat::new(3, 4).unwrap(), Rat::zero()),
];
assert_eq!(nary::weighted_mean(&pairs), Some(Rat::new(1, 4).unwrap()));
assert_eq!(nary::weighted_mean(&[]), None);
```

The accumulation bounds are proven (V8 below): `sum` and `product` are within
`k · m · 2^-61` after `k` steps, with `|factor| ≤ 1` for `product`, and
`weighted_mean` is within `8k · 2^-61 / δ` when weights and values lie in
`[0, 1]` and the exact weight sum is at least `δ`.

## Conversions and serialisation

`f64` in, by `from_f64_dir` (partial, directed) or `q_from_f64` (total).
`f64` out, by `to_f64`, which is for display: it makes three roundings and is
one of the three trusted functions (`TRUSTED.md`). There is deliberately no
`Q → f64`, because no float honestly denotes `PosSat`.

```rust
use the_q::{Dir, Q, Rat, from_f64_dir, q_from_f64, to_f64};

// `0.1f64` is not one tenth; the conversion is exact about the double.
let tenth = from_f64_dir(0.1, Dir::Nearest).unwrap();
assert_eq!(
    tenth,
    Rat::new(3_602_879_701_896_397, 36_028_797_018_963_968).unwrap()
);
assert_ne!(tenth, Rat::from_decimal(1, 1).unwrap());

// Directed conversion brackets the double when it does not fit exactly.
let lo = from_f64_dir(1e-300, Dir::Down).unwrap();
let hi = from_f64_dir(1e-300, Dir::Up).unwrap();
assert!(lo <= hi);

// `None` for NaN, infinity, and magnitudes above 2^61.
assert_eq!(from_f64_dir(f64::NAN, Dir::Nearest), None);
assert_eq!(from_f64_dir(1e300, Dir::Nearest), None);

// `q_from_f64` is total. There is no `Q -> f64`: nothing denotes `PosSat`.
assert_eq!(q_from_f64(f64::INFINITY), Q::PosInf);
assert_eq!(q_from_f64(f64::NAN), Q::Nan);
assert_eq!(q_from_f64(1e300), Q::PosSat);
assert_eq!(q_from_f64(0.5), Q::new(1, 2));

// `to_f64` is for display; three roundings, do not feed it back in.
assert_eq!(to_f64(Rat::new(1, 4).unwrap()), 0.25);
```

### Wider inputs: `i128` pairs and decimals

Two always-available cores take anything an `i128` can express. Both have an
exact variant that returns `None` the moment ingestion itself would have to
round, so an `Exact` built from it denotes the original value, not merely a
`Rat` that needs no *further* rounding.

```rust
use the_q::{Dir, MAX_DECIMAL_MANTISSA, MAX_DECIMAL_SCALE, MAX_MAG, Rat};
use the_q::{
    from_decimal128_dir, from_decimal128_exact, from_ratio128_dir, from_ratio128_exact,
};

// `mantissa · 10^-scale` with an `i128` mantissa and a scale up to 28:
// the domain of a `rust_decimal::Decimal`, exact whenever it fits.
assert_eq!(
    from_decimal128_dir(1999, 2, Dir::Nearest),
    Rat::new(1999, 100)
);
assert_eq!(from_decimal128_exact(85, 2), Rat::new(17, 20));
assert_eq!(
    from_decimal128_dir(1, MAX_DECIMAL_SCALE + 1, Dir::Nearest),
    None
);

// A 96-bit mantissa at scale 28 does not reduce into the budget: the
// directed conversion rounds, the exact one refuses.
let lo = from_decimal128_dir(MAX_DECIMAL_MANTISSA, 28, Dir::Down).unwrap();
let hi = from_decimal128_dir(MAX_DECIMAL_MANTISSA, 28, Dir::Up).unwrap();
assert!(lo < hi);
assert_eq!(from_decimal128_exact(MAX_DECIMAL_MANTISSA, 28), None);

// Any `i128` pair, sign-normalised: the core every library adapter uses.
assert_eq!(from_ratio128_dir(-3, -4, Dir::Nearest), Rat::new(3, 4));
assert_eq!(from_ratio128_dir(1, 0, Dir::Nearest), None);
assert_eq!(from_ratio128_exact(1, i128::from(MAX_MAG) + 2), None);
assert!(from_ratio128_dir(1, i128::from(MAX_MAG) + 2, Dir::Nearest).is_some());
```

### Other numeric libraries

Each feature-gated adapter reduces its library's representation to an `i128`
pair and hands it to the cores above. Each comes in the same three tiers: a
directed `Rat` function, a total `Q` function (also `impl From`) that rounds to
nearest and saturates by sign, and an `Exact` function (also `impl TryFrom`,
except for `fixed`) that refuses rather than rounds.

```rust
use rust_decimal::Decimal;
use the_q::{Dir, Exact, ExactError, Q, Rat};
use the_q::{exact_from_rust_decimal, from_rust_decimal_dir, q_from_rust_decimal};

let d = Decimal::new(85, 2); // 0.85
assert_eq!(
    from_rust_decimal_dir(d, Dir::Nearest),
    Rat::new(17, 20).unwrap()
);
assert_eq!(Q::from(d), Q::new(17, 20));
assert_eq!(
    Exact::try_from(d),
    Ok(Exact::new(Rat::new(17, 20).unwrap()))
);

// Past the budget: `Q` saturates by sign, `Exact` refuses.
assert_eq!(q_from_rust_decimal(Decimal::MAX), Q::PosSat);
assert_eq!(
    exact_from_rust_decimal(Decimal::MAX),
    Err(ExactError::Inexact)
);
```

```rust
use fixed::types::I64F64;
use the_q::{Dir, Q, Rat};
use the_q::{exact_from_fixed, from_fixed_dir, q_from_fixed};

// One generic function for every 128-bit-backed `fixed` type.
let v = I64F64::from_num(-1.25);
assert_eq!(from_fixed_dir(v, Dir::Nearest), Rat::new(-5, 4));
assert_eq!(q_from_fixed(v), Q::new(-5, 4));
assert_eq!(
    exact_from_fixed(v).map(|e| e.value()),
    Ok(Rat::new(-5, 4).unwrap())
);
assert_eq!(q_from_fixed(I64F64::from_num(i64::MAX)), Q::PosSat);
```

`fixed` gets no `From`/`TryFrom` impls: a blanket impl over every `Fixed` type
cannot coexist with the concrete impl for `Decimal`.

```rust
use num_bigint::BigInt;
use num_rational::{BigRational, Ratio};
use the_q::{Dir, Q, Rat};
use the_q::{from_big_rational_dir, from_num_rational_i64_exact, q_from_big_rational};

// `Ratio<i64>` is always exact: its invariant is the one `Rat` needs.
assert_eq!(
    from_num_rational_i64_exact(Ratio::new(3i64, 4)),
    Rat::new(3, 4)
);
assert_eq!(Q::from(Ratio::new(-7i64, 3)), Q::new(-7, 3));

// `BigRational` needs an `i128` extraction first; when its reduced terms
// are too wide, the `Q` conversion falls back to `to_f64` and the `Rat`
// conversion is `None`.
let v = BigRational::new(BigInt::from(22), BigInt::from(7));
assert_eq!(from_big_rational_dir(&v, Dir::Nearest), Rat::new(22, 7));
let wide = BigRational::new(BigInt::from(10).pow(40) + 1, BigInt::from(10).pow(40));
assert_eq!(from_big_rational_dir(&wide, Dir::Nearest), None);
assert_eq!(q_from_big_rational(&wide), Q::one()); // via f64, lossy
```

The `to_f64` fallback exists because `Ratio` keeps its terms in lowest form and
nothing bounds *those* by the value's magnitude: `(10^40 + 1) / 10^40` is a
value near 1 whose terms fit no `i128`. Guessing a saturation sign would be
wrong, so the `Q` conversion goes through a double instead and says so in its
docs.

```rust
use num_bigint::BigInt;
use the_q::{Dir, ExactError, Q, Rat};
use the_q::{exact_from_bigint, from_bigint_dir, q_from_bigint};

assert_eq!(
    from_bigint_dir(&BigInt::from(-42), Dir::Nearest),
    Rat::new(-42, 1)
);
// An integer's magnitude is its value, so "too wide" always means saturation.
let huge = BigInt::from(10).pow(40);
assert_eq!(q_from_bigint(&huge), Q::PosSat);
assert_eq!(exact_from_bigint(&huge), Err(ExactError::Inexact));
```

```rust
use bigdecimal::BigDecimal;
use std::str::FromStr;
use the_q::{Dir, Q, Rat};
use the_q::{from_bigdecimal_dir, from_bigdecimal_exact, q_from_bigdecimal};

let v = BigDecimal::from_str("-3.14").unwrap();
assert_eq!(from_bigdecimal_dir(&v, Dir::Nearest), Rat::new(-157, 50));
assert_eq!(from_bigdecimal_exact(&v), Rat::new(-157, 50));
// A negative scale is a large integer, still exact.
assert_eq!(
    Q::from(BigDecimal::from_str("1.2e3").unwrap()),
    Q::new(1200, 1)
);
assert_eq!(
    q_from_bigdecimal(&BigDecimal::from_str("1e30").unwrap()),
    Q::PosSat
);
```

With the `serde` feature, `Rat` encodes as the exact `[num, den]` pair and `Q`
as that pair or the special's string. The encoding is untagged, so it decodes
only in self-describing formats. Decoding re-canonicalises through `Rat::new`
and rejects a malformed payload rather than constructing an invalid value.

```rust
use the_q::{Q, Rat};

// `Rat` is the exact `[num, den]` pair; `Q` specials are strings.
let x = Rat::new(17, 20).unwrap();
assert_eq!(serde_json::to_string(&x).unwrap(), "[17,20]");
assert_eq!(serde_json::from_str::<Rat>("[17,20]").unwrap(), x);
assert_eq!(serde_json::to_string(&Q::PosSat).unwrap(), "\">max\"");
assert_eq!(serde_json::from_str::<Q>("\"nan\"").unwrap(), Q::Nan);

// Decoding re-canonicalises and rejects a malformed pair.
assert_eq!(
    serde_json::from_str::<Rat>("[6,8]").unwrap(),
    Rat::new(3, 4).unwrap()
);
assert!(serde_json::from_str::<Rat>("[1,0]").is_err());
```

## The rounding contract

When an exact result does not fit, it snaps to a dyadic grid chosen per
magnitude: with `k = bitlen(floor(|x|))`, the grid step is `2^-(62-k)`, capped
at `2^-61`. Ties go to even. Proven, for every operation:

| rule | statement |
|---|---|
| R1 | a representable exact result is returned unchanged |
| R2 | `Dir::Down` ≤ exact ≤ `Dir::Up` |
| R3 | error ≤ `2^-61 · max(1, \|exact\|)` in every direction; `2^-62` for `Dir::Nearest`, which `add`/`sub`/`mul`/`div` use |
| R4 | rounding is monotone on a fixed grid |

R3 is **absolute below 1**. A result near 1 carries about 61 significant bits;
a result near `2^-40` carries about 21; below `2^-62` a value rounds to zero.
This is the single most important thing to know before using the crate for
small quantities, and it governs every accuracy figure above. If small values
matter, scale the problem.

## Limits

**Not associative.** `add` and `mul` are commutative with rounding. They are
associative and distributive only on the exact path (no intermediate rounds),
and that is proven. The general failure is bounded:
`|((a+b)+c) − (a+(b+c))| ≤ 4 · 2^-61 · m` for any bound `m ≥ 1` on the partial
sums, and `|((a·b)·c) − (a·(b·c))| ≤ 6 · 2^-61` on `[0, 1]`. `Exact` gives the
laws back in exchange for refusing to round.

**Not globally monotone.** R4 holds on each grid, not across the
representable/rounded boundary. Counterexample (`tests/adversarial.rs`):

```text
u = 2 / (2^61 + 1)              representable, returned exactly
v = u · (1 + 1/(2^62 − 2))      a hair larger, not representable
round_down(v) = 2^-61  <  u = round_down(u)       though u < v
```

The cause is that `round` has no single codomain: a representable input is
returned from the whole bounded-denominator set, an unrepresentable one is
snapped to the far coarser dyadic subgrid. Projection onto any one fixed set
would be monotone. Fixing it means either always snapping, which discards
exactness, or a Stern–Brocot floor onto the full set, which is the harder proof.
The crate does neither; if you iterate a rounded projection to a fixed point,
know this.

**Saturation is a choice.** Some exact results above `2^62 − 1` do have a
`Rat` within `2^-61` (`saturation::lemma_saturation_is_a_choice` exhibits one).
R3 is scoped below the ceiling to keep one clean boundary, and results above it
saturate. `Rat::new` also returns `None` for an `i64` pair that is already
reduced but over budget; `Rat::new_rounded` is total in the numerator.

**`Q` is not a semiring.** Its `add` and `mul` are commutative
unconditionally, but associative, distributive and monotone only on the
all-`Number` exact path, exactly as for `Rat`. Once a `PosSat`/`NegSat` is
reachable all three fail; `mul` additionally fails to associate on values that
never touch saturation, because rounding a product to zero can manufacture a
`0 · ∞` that exact arithmetic never would. `Q::div(a, b) == Q::mul(a,
Q::recip(b))` fails in six cells. No defect bound is stated at this level:
`Nan` and the unbounded saturation intervals carry no metric to bound against.
Every failure has a test in `tests/q_laws.rs`.

**Transcendentals are exact at rational points only where a proof says so.**
`cbrt(8)` is `2305843009213693951 / 2^60`, within `2^-60` of 2 but not 2, and
`exp2(3)` is likewise a hair under 8, because both go through `exp(ln)` and
those are series. `sqrt` of a perfect square, `exp(0)`, `ln(1)`, `log2` at a
power of two and `log10` at a power of ten return the integer, and for the two
logarithms that is a proven postcondition (`log2(2^k) == k` for `k ≤ 61`,
`log10(10^k) == k` for `k ≤ 18`, both signs, every power a `Rat` holds). Everything else lands near the
true value by the measured margins above, not on it.

## What is proven

`1219 verified, 0 errors` in CI; no `assume`, no `admit`; three
`external_body` functions, enumerated in `TRUSTED.md`.

* **V1** Every public operation preserves canonical form and the budget.
* **V2** No panic, no overflow: every `i128` intermediate is bounded. The
  `2^62` budget is exactly what makes cross-multiplied products fit.
* **V3** Every result equals the exact rational model, stated division-free.
* **V4** R1–R4 above, with the tighter nearest bound.
* **V5** GCD correctness and termination.
* **V6** Commutativity; exact-path associativity and distributivity; identity
  and involution laws; a total order agreeing with the value order.
* **V7** Lipschitz bounds for `add`, `mul`, `recip`, `div`.
* **V8** Accumulation bounds: `sum` and `product` within `k · m · 2^-61` after
  `k` steps (`product` needs `|factor| ≤ 1`); `weighted_mean`'s returned value
  within `8k · 2^-61 / δ` when weights and values lie in `[0, 1]` and the exact
  weight sum is at least `δ`.
* **V9** `Q`: totality, classification, total order, `Nan` absorption.
* **V10** Transcendentals: totality and termination. `isqrt` is exactly the
  integer square root; `log2` returns exactly `k` on `2^k` and `1/2^k`, and
  `log10` exactly `k` on `10^k` and `1/10^k`, for every such power a `Rat`
  holds.
* **V11** `Q`'s algebraic laws (commutative unconditionally; associative,
  distributive and monotone on the all-`Number` exact path and nowhere
  further), and the containment obligation `{x ⊕ y : x ∈ ⟦a⟧, y ∈ ⟦b⟧} ⊆
  ⟦op(a, b)⟧` for the special-value propagation of `add`, `sub`, `mul` and
  `div`, proven against an independent ghost model of true values
  (`denote.rs`) rather than tested against the table alone. Soundness, and
  honesty (`Nan` is returned whenever a genuine indeterminate such as `∞ − ∞`
  or `0 · ∞` can be witnessed), for all four; necessity (`Nan` is never
  returned where a smaller state would also be sound) for one cell as the
  pattern.
* The associativity bounds under Limits, interval enclosure, the `Exact` laws,
  the `i128` conversion cores, and the value pinning of every constructor
  including the `f64` decomposition's integer core.

**Not proven**: the `f64` decode/encode (trusted, tested); transcendental
accuracy (measured, above); `pow_u32`'s value (only its well-formedness);
`mul` associativity outside `[0, 1]`; the `Q` folds against the containment
model (a set-valued induction, tracked as follow-on work); `Nan` necessity for
every `mul`/`div` cell; the feature-gated library adapters, which call into
foreign types Verus has no model of and sit outside `verus!` as thin wrappers
over the verified cores.

## Testing

`malachite-q` is the oracle, as a dev-dependency only (`scripts/check-no-lgpl.sh`
enforces this). `tests/oracle.rs` runs 20,000 random cases per operation per
direction against R1–R3 plus every `p/q` with `|p|, q ≤ 12`; `tests/bounds.rs`
checks R3's nearest bound, the weighted-mean bound and interval enclosure on
random operands; `tests/props.rs` covers the invariant, the laws, and
byte-identical results across eight threads; `tests/adversarial.rs` holds the
budget edges and both counterexamples; `tests/transcendental.rs` carries the
accuracy oracles; `tests/q_laws.rs` the counterexamples to `Q`'s laws;
`tests/ratio_core.rs` and one suite per library integration the conversion
boundary; `tests/readme_examples.rs` compiles and runs every code block on this
page and fails if one drifts from this file. Every public function has a
doctest. Overflow checks stay on in release.

## Performance

`cargo bench --bench arith`: minimum of seven runs, `overflow-checks = true`.
Linux 6.16 x86-64, rustc 1.96. The benchmark prints its own quality block; on
this run control drift was 5.8% and the widest spread 137%, so treat the second
digit as noise.

| op | the-q | `num-rational` `Ratio<i64>` | `malachite-q` (exact) | `f64` |
|---|---:|---:|---:|---:|
| `add` | 56 ns | 127 ns | 110 ns | 1.3 ns |
| `mul` | 62 ns | 150 ns | 147 ns | 1.3 ns |
| `div` | 62 ns | 160 ns | 131 ns | 1.3 ns |
| compare | 2.6 ns | 28 ns | 68 ns | 1.4 ns |

Those are exact-path costs. Rounding is the expensive path, and it is where
the exact backend wins:

| `Rat::add` path | the-q | exact |
|---|---:|---:|
| no rounding | 14 ns | 49 ns |
| rounded | 349 ns | 148 ns |
| saturated | 137 ns | 46 ns |

| chain `acc = (acc + x) · y`, per step | the-q | exact | exact digits |
|---|---:|---:|---:|
| `k = 4` | 195 ns | 326 ns | 29 |
| `k = 64` | 1400 ns | 443 ns | 311 |
| `k = 1024` | 1503 ns | 1093 ns | 2 979 |
| `k = 4096` | 1619 ns | 2609 ns | 8 806 |

`the-q` plateaus once operands fill the budget; the exact backend grows without
bound and is cheaper between roughly `k = 8` and `k = 2000`. An 8-pair
`weighted_mean` is 8.0 µs against 5.3 µs exact. Transcendentals: `exp` 0.6 µs,
`ln` 1.5 µs, `sqrt` 11 µs, `sin`/`cos` 17–19 µs, `atan` 32 µs.

## Verification

Specifications and proofs live in the source inside `verus!` blocks. `cargo
build` compiles them with plain rustc; `cargo verus verify` checks them.
`VERIFICATION.md` has the obligation map and reproduction steps; `TRUSTED.md`
the three trusted functions; `docs/SPEC.md` the original specification with its
six recorded departures.

```sh
cargo test --locked --all-features          # includes every integration suite
cargo verus verify --locked --all-features -- --multiple-errors 8
```

## Licence

Dual-licensed. Free under AGPL-3.0-or-later: use, modify, and redistribute
freely, including as a network service, as long as you release your source
under the same terms (`AGPL-3.0-or-later` section 13, the network-use
clause, applies to any service built on this crate, not only to
redistributed binaries). If that obligation does not work for your use, which
covers most commercial and closed-source use, a separate commercial licence is
available; contact the author for terms.

The LGPL-3.0-only oracle `malachite-q` is a dev-dependency only and never
ships, so its terms do not apply to any release of this crate.
