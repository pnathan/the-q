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
//! and the measurement is the minimum of seven timed runs. The inputs are
//! deterministic (splitmix64, fixed seed). A re-run therefore compares against
//! the same work.
//!
//! The statistic is the minimum and not the median, and the run ends with a
//! measurement-quality report. Both exist because a comparison between two
//! builds is only as good as the noise floor of the machine that produced it.
//! Contention moves a median; it cannot move the minimum below the true cost.
//! The report states the widest spread seen in any single measurement, and the
//! drift of a control workload that no change to this crate can affect. A
//! difference between two builds that is smaller than the control drift is not
//! a result.
//!
//! Run this benchmark with `cargo bench`. The `bench` profile inherits
//! `release`, and this crate builds `release` with `overflow-checks = true`.
//! The numbers below therefore describe the shipped configuration, not a faster
//! one.

use std::hint::black_box;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::Instant;

use malachite_q::Rational;
use the_q::{Q, Rat, nary};

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

/// The widest spread seen in any single measurement, in per mille of that
/// measurement's minimum. `time_ns` updates it; the report at the end of the
/// run prints it.
static WORST_SPREAD_PERMILLE: AtomicU64 = AtomicU64::new(0);

/// Returns the minimum of `REPS` timed runs, in ns per iteration. `WARMUP`
/// untimed runs precede the timed runs.
///
/// The minimum is the statistic here. Every source of noise on a machine adds
/// time; none removes it. The minimum is therefore the sample least polluted by
/// whatever else the machine was doing, and it is the statistic that makes two
/// builds comparable. The spread between the minimum and the maximum goes to
/// the measurement-quality report.
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
    let min = samples[0];
    let max = samples[samples.len() - 1];
    let spread = ((max - min) / min * 1000.0) as u64;
    WORST_SPREAD_PERMILLE.fetch_max(spread, Ordering::Relaxed);
    min
}

/// A fixed integer workload, used as a control.
///
/// No change to this crate can alter what this function costs. Measuring it at
/// the start and at the end of the run therefore measures the machine, and the
/// difference between the two is the drift a build-to-build comparison has to
/// beat before it means anything.
fn control() -> f64 {
    time_ns(20_000, |i| {
        let mut acc = i as u64 | 1;
        for _ in 0..16 {
            acc = acc.wrapping_mul(0x9E37_79B9_7F4A_7C15) ^ (acc >> 29);
        }
        acc
    })
}

/// Prints the control drift and the widest spread, with a verdict.
fn quality_report(first: f64, last: f64) {
    let drift = (last - first).abs() / first * 100.0;
    let spread = WORST_SPREAD_PERMILLE.load(Ordering::Relaxed) as f64 / 10.0;
    println!("\n### Measurement quality\n");
    println!("| statistic | value |");
    println!("|---|---:|");
    println!("| control, first measurement | {first:.2} ns |");
    println!("| control, last measurement | {last:.2} ns |");
    println!("| control drift | {drift:.1}% |");
    println!("| widest spread in one measurement | {spread:.1}% |");
    println!();
    if drift > 5.0 || spread > 25.0 {
        println!(
            "The machine was not quiet. A difference between two builds of less\n\
             than {:.0}% is noise, not a result. Re-run on an idle machine, or\n\
             pin the benchmark to one core and interleave the two builds.",
            drift.max(5.0)
        );
    } else {
        println!(
            "The machine was quiet. A difference between two builds of more than\n\
             about {:.0}% is a result.",
            drift.max(2.0)
        );
    }
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
    let control_first = control();
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

    println!("the-q benchmark — {n} distinct operand pairs, minimum of {REPS} runs");
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

    quality_report(control_first, control());
}
