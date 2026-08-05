//! This benchmark compares `the-q` against the two things it sits between:
//! hardware `f64`, and an exact arbitrary-precision rational (`malachite-q`,
//! the crate's differential oracle).
//!
//! The primary measurement is not the single-operation cost. It is the change
//! in that cost as a computation gets longer. `Rat` and `f64` are both
//! fixed-width. Their per-operation cost is therefore flat in the length of the
//! chain. An exact rational's denominators multiply. Its per-operation cost
//! therefore grows without bound. The chain section below measures that growth.
//! That growth is the reason a bounded rational exists.
//!
//! This benchmark does not use criterion. Criterion is a new dev-dependency,
//! and the measurement is a median of seven timed runs. The inputs are
//! deterministic (splitmix64, fixed seed). A re-run therefore compares against
//! the same work.
//!
//! Run this benchmark with `cargo bench`. The `bench` profile inherits
//! `release`, and this crate builds `release` with `overflow-checks = true`.
//! The numbers below therefore describe the shipped configuration, not a faster
//! one.

use std::hint::black_box;
use std::time::Instant;

use malachite_q::Rational;
use the_q::{nary, Rat, Q};

/// splitmix64 with a fixed seed. The fixed seed gives repeatability. It does
/// not give statistical quality.
struct Rng(u64);

impl Rng {
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    /// Returns a fraction in `(0, 1]` with a denominator under 10_000. This is
    /// the shape of an opinion value. It is also small enough to keep the
    /// initial cost of the exact backend low.
    fn next_frac(&mut self) -> (i64, i64) {
        let den = (self.next_u64() % 9_999 + 1) as i64;
        let num = (self.next_u64() % (den as u64) + 1) as i64;
        (num, den)
    }
}

const WARMUP: usize = 3;
const REPS: usize = 7;

/// Returns the median of `REPS` timed runs, in ns per iteration. `WARMUP`
/// untimed runs precede the timed runs.
fn time_ns<T>(iters: usize, mut f: impl FnMut(usize) -> T) -> f64 {
    let mut samples = Vec::with_capacity(REPS);
    for r in 0..(WARMUP + REPS) {
        let start = Instant::now();
        for i in 0..iters {
            black_box(f(i));
        }
        let per = start.elapsed().as_nanos() as f64 / iters as f64;
        if r >= WARMUP {
            samples.push(per);
        }
    }
    samples.sort_by(|a, b| a.partial_cmp(b).expect("no NaN timings"));
    samples[samples.len() / 2]
}

fn row(op: &str, q: f64, f: f64, r: f64) {
    println!(
        "| {:<14} | {:>9.1} | {:>9.1} | {:>11.1} | {:>7.1}x | {:>7.1}x |",
        op,
        q,
        f,
        r,
        q / f,
        r / q
    );
}

/// Prints a two-column row. This row covers the functions that `f64` has and an
/// exact rational does not. `malachite-q` has no square root or exponential for
/// comparison.
fn row2(op: &str, q: f64, f: f64) {
    println!("| {:<14} | {:>9.1} | {:>9.1} | {:>7.1}x |", op, q, f, q / f);
}

fn header2(title: &str) {
    println!("\n### {title}\n");
    println!(
        "| {:<14} | {:>9} | {:>9} | {:>8} |",
        "op", "the-q ns", "f64 ns", "q/f64"
    );
    println!("|{:-<16}|{:->11}|{:->11}|{:->10}|", "", "", "", "");
}

fn header(title: &str) {
    println!("\n### {title}\n");
    println!(
        "| {:<14} | {:>9} | {:>9} | {:>11} | {:>8} | {:>8} |",
        "op", "the-q ns", "f64 ns", "exact ns", "q/f64", "exact/q"
    );
    println!(
        "|{:-<16}|{:->11}|{:->11}|{:->13}|{:->10}|{:->10}|",
        "", "", "", "", "", ""
    );
}

fn main() {
    let n = 1 << 12;
    let mut rng = Rng(0x1234_5678);

    let raw: Vec<(i64, i64)> = (0..2 * n).map(|_| rng.next_frac()).collect();
    let qs: Vec<Rat> = raw
        .iter()
        .map(|&(a, b)| Rat::new(a, b).expect("den != 0 and both fit"))
        .collect();
    let fs: Vec<f64> = raw.iter().map(|&(a, b)| a as f64 / b as f64).collect();
    let rs: Vec<Rational> = raw
        .iter()
        .map(|&(a, b)| Rational::from_signeds(a, b))
        .collect();

    println!("the-q benchmark — {n} distinct operand pairs, median of {REPS} runs");
    println!("exact = malachite-q Rational (arbitrary precision, the differential oracle)");

    header("Single operations");

    let m = |i: usize| (i % n, n + (i % n));

    row(
        "add",
        time_ns(n, |i| {
            let (a, b) = m(i);
            Rat::add(qs[a], qs[b])
        }),
        time_ns(n, |i| {
            let (a, b) = m(i);
            fs[a] + fs[b]
        }),
        time_ns(n, |i| {
            let (a, b) = m(i);
            &rs[a] + &rs[b]
        }),
    );

    row(
        "sub",
        time_ns(n, |i| {
            let (a, b) = m(i);
            Rat::sub(qs[a], qs[b])
        }),
        time_ns(n, |i| {
            let (a, b) = m(i);
            fs[a] - fs[b]
        }),
        time_ns(n, |i| {
            let (a, b) = m(i);
            &rs[a] - &rs[b]
        }),
    );

    row(
        "mul",
        time_ns(n, |i| {
            let (a, b) = m(i);
            Rat::mul(qs[a], qs[b])
        }),
        time_ns(n, |i| {
            let (a, b) = m(i);
            fs[a] * fs[b]
        }),
        time_ns(n, |i| {
            let (a, b) = m(i);
            &rs[a] * &rs[b]
        }),
    );

    row(
        "div",
        time_ns(n, |i| {
            let (a, b) = m(i);
            Rat::div(qs[a], qs[b])
        }),
        time_ns(n, |i| {
            let (a, b) = m(i);
            fs[a] / fs[b]
        }),
        time_ns(n, |i| {
            let (a, b) = m(i);
            &rs[a] / &rs[b]
        }),
    );

    row(
        "compare",
        time_ns(n, |i| {
            let (a, b) = m(i);
            Rat::lt(qs[a], qs[b])
        }),
        time_ns(n, |i| {
            let (a, b) = m(i);
            fs[a] < fs[b]
        }),
        time_ns(n, |i| {
            let (a, b) = m(i);
            rs[a] < rs[b]
        }),
    );

    // This section is the primary measurement. It runs `acc = (acc + x) * y`
    // for k steps and reports the cost per step. `Rat` and `f64` stay at 16 and
    // 8 bytes at every depth. The exact backend's operands grow, so its
    // per-step cost grows with them. The last column reports the size of the
    // exact result, which is the quantity that grows.
    println!("\n### Chained fusion, cost per step at depth k\n");
    println!(
        "| {:<14} | {:>9} | {:>9} | {:>11} | {:>8} | {:>8} | {:>12} |",
        "depth", "the-q ns", "f64 ns", "exact ns", "q/f64", "exact/q", "exact digits"
    );
    println!(
        "|{:-<16}|{:->11}|{:->11}|{:->13}|{:->10}|{:->10}|{:->14}|",
        "", "", "", "", "", "", ""
    );

    for k in [4usize, 16, 64, 256, 1024, 4096] {
        // The outer iteration count falls as k grows. The total work therefore
        // stays comparable across depths.
        let iters = (n / k).max(4);

        let q = time_ns(iters, |i| {
            let mut acc = qs[i % n];
            for j in 0..k {
                acc = Rat::mul(Rat::add(acc, qs[(i + j) % n]), qs[(i + j + 1) % n]);
            }
            acc
        }) / k as f64;

        let f = time_ns(iters, |i| {
            let mut acc = fs[i % n];
            for j in 0..k {
                acc = (acc + fs[(i + j) % n]) * fs[(i + j + 1) % n];
            }
            acc
        }) / k as f64;

        let r = time_ns(iters, |i| {
            let mut acc = rs[i % n].clone();
            for j in 0..k {
                acc = (acc + &rs[(i + j) % n]) * &rs[(i + j + 1) % n];
            }
            acc
        }) / k as f64;

        // This measures the size of the exact answer, in decimal characters of
        // "num/den". `Rat` stays at 16 bytes here, and `f64` stays at 8.
        let mut acc = rs[0].clone();
        for j in 0..k {
            acc = (acc + &rs[j % n]) * &rs[(j + 1) % n];
        }
        let digits = acc.to_string().len();

        println!(
            "| {:<14} | {:>9.1} | {:>9.1} | {:>11.1} | {:>7.1}x | {:>7.1}x | {:>12} |",
            format!("k = {k}"),
            q,
            f,
            r,
            q / f,
            r / q,
            digits
        );
    }

    header("weighted_mean over 8 (weight, value) pairs");

    let w = 8usize;
    // The pairs are built once, outside the timed region. `weighted_mean` takes
    // a slice. The other two backends pay no `Vec` allocation, so timing that
    // allocation would measure the harness instead of the arithmetic.
    let qpairs: Vec<(Rat, Rat)> = (0..n + w).map(|j| (qs[j % n], qs[(j + 1) % n])).collect();
    let q = time_ns(n / w, |i| {
        let start = (i * w) % n;
        nary::weighted_mean(&qpairs[start..start + w])
    });
    let f = time_ns(n / w, |i| {
        let mut num = 0.0f64;
        let mut den = 0.0f64;
        for j in 0..w {
            let wt = fs[(i * w + j) % n];
            num += wt * fs[(i * w + j + 1) % n];
            den += wt;
        }
        num / den
    });
    let r = time_ns(n / w, |i| {
        let mut num = Rational::from(0);
        let mut den = Rational::from(0);
        for j in 0..w {
            let wt = &rs[(i * w + j) % n];
            num += wt * &rs[(i * w + j + 1) % n];
            den += wt;
        }
        num / den
    });
    row("weighted_mean", q, f, r);

    // -----------------------------------------------------------------------
    // The extended type. Every operation here is total. The comparison is
    // therefore against `f64`'s equally total arithmetic, and not against
    // `Rat`'s partial arithmetic. This section measures the cost of totality.
    // -----------------------------------------------------------------------

    let exs: Vec<Q> = qs.iter().map(|x| Q::Number(*x)).collect();

    header2("extended Q (total arithmetic) vs f64");

    let q = time_ns(n, |i| Q::add(exs[i % n], exs[(i + 1) % n]));
    let f = time_ns(n, |i| fs[i % n] + fs[(i + 1) % n]);
    row2("Q::add", q, f);

    let q = time_ns(n, |i| Q::mul(exs[i % n], exs[(i + 1) % n]));
    let f = time_ns(n, |i| fs[i % n] * fs[(i + 1) % n]);
    row2("Q::mul", q, f);

    // Division shows the difference most clearly. `Q::div` cannot panic and
    // needs no guard. `Rat::div` requires the caller to rule out a zero
    // divisor.
    let q = time_ns(n, |i| Q::div(exs[i % n], exs[(i + 1) % n]));
    let f = time_ns(n, |i| fs[i % n] / fs[(i + 1) % n]);
    row2("Q::div", q, f);

    let q = time_ns(n, |i| Q::compare(exs[i % n], exs[(i + 1) % n]));
    let f = time_ns(n, |i| fs[i % n].partial_cmp(&fs[(i + 1) % n]));
    row2("Q::compare", q, f);

    // -----------------------------------------------------------------------
    // Transcendentals. `f64` runs these in hardware, and this crate evaluates a
    // series in software. A large ratio is therefore expected. The useful
    // number is the absolute cost, which shows whether the function is usable.
    // -----------------------------------------------------------------------

    header2("transcendentals vs f64 (hardware)");

    let q = time_ns(n, |i| exs[i % n].sqrt());
    let f = time_ns(n, |i| fs[i % n].sqrt());
    row2("sqrt", q, f);

    let q = time_ns(n, |i| exs[i % n].exp());
    let f = time_ns(n, |i| fs[i % n].exp());
    row2("exp", q, f);

    let q = time_ns(n, |i| exs[i % n].ln());
    let f = time_ns(n, |i| fs[i % n].ln());
    row2("ln", q, f);

    let q = time_ns(n, |i| exs[i % n].sin());
    let f = time_ns(n, |i| fs[i % n].sin());
    row2("sin", q, f);

    let q = time_ns(n, |i| exs[i % n].cos());
    let f = time_ns(n, |i| fs[i % n].cos());
    row2("cos", q, f);

    let q = time_ns(n, |i| exs[i % n].atan());
    let f = time_ns(n, |i| fs[i % n].atan());
    row2("atan", q, f);

    println!();
}
