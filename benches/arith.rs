//! `the-q` against the two things it sits between: hardware `f64`, and an exact
//! arbitrary-precision rational (`malachite-q`, the crate's differential oracle).
//!
//! The interesting number is not the single-operation cost — it is what happens
//! to that cost as a computation gets longer. `Q` and `f64` are both fixed-width,
//! so their per-operation cost is flat in the length of the chain. An exact
//! rational's denominators multiply, so its per-operation cost grows without
//! bound. `chain` below measures exactly that, and it is the reason a bounded
//! rational exists at all.
//!
//! No criterion: it would be a new dev-dependency for something that is a median
//! of seven timed runs. Deterministic inputs (splitmix64, fixed seed), so
//! re-running compares against the same work.
//!
//! Run with `cargo bench`. Note that the `bench` profile inherits `release`,
//! which this crate builds with `overflow-checks = true` — the numbers below
//! are for the configuration the crate actually ships, not a faster one.

use std::hint::black_box;
use std::time::Instant;

use malachite_q::Rational;
use the_q::{nary, Q};

/// splitmix64. Fixed seed: the point is repeatability, not statistics.
struct Rng(u64);

impl Rng {
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    /// A fraction in `(0, 1]` with a denominator under 10_000 — the shape of an
    /// opinion value, and small enough that the exact backend starts cheap.
    fn next_frac(&mut self) -> (i64, i64) {
        let den = (self.next_u64() % 9_999 + 1) as i64;
        let num = (self.next_u64() % (den as u64) + 1) as i64;
        (num, den)
    }
}

const WARMUP: usize = 3;
const REPS: usize = 7;

/// Median of `REPS` timed runs after `WARMUP` untimed ones, in ns per iteration.
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
    let qs: Vec<Q> = raw
        .iter()
        .map(|&(a, b)| Q::new(a, b).expect("den != 0 and both fit"))
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
            Q::add(qs[a], qs[b])
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
            Q::sub(qs[a], qs[b])
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
            Q::mul(qs[a], qs[b])
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
            Q::div(qs[a], qs[b])
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
            Q::lt(qs[a], qs[b])
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

    // The point of the whole exercise. `acc = (acc + x) * y`, k steps, measured
    // per step. `Q` and `f64` are 16 and 8 bytes at every depth; the exact
    // backend's operands grow, so its per-step cost has to grow with them. The
    // last column is the size of the exact result, which is what is growing.
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
        // Fewer outer iterations as k grows, so total work stays comparable.
        let iters = (n / k).max(4);

        let q = time_ns(iters, |i| {
            let mut acc = qs[i % n];
            for j in 0..k {
                acc = Q::mul(Q::add(acc, qs[(i + j) % n]), qs[(i + j + 1) % n]);
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

        // How big the exact answer actually got, as decimal characters of
        // "num/den". `Q` is 16 bytes here regardless, and `f64` is 8.
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
    // Built once, outside the timed region: `weighted_mean` takes a slice, and
    // timing a `Vec` allocation for `Q` that the other two backends do not pay
    // would be measuring the harness rather than the arithmetic.
    let qpairs: Vec<(Q, Q)> = (0..n + w).map(|j| (qs[j % n], qs[(j + 1) % n])).collect();
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

    println!();
}
