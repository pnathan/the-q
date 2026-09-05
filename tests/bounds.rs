//! Bounds on random operands against `malachite-q`: R2/R3 with the tighter
//! nearest bound, the composed `weighted_mean` bound, and interval enclosure.
//! `dump_transcendentals` (ignored) writes `target/accuracy-dump.tsv` for the
//! two independent oracles in `scripts/accuracy/`.
use malachite_base::num::arithmetic::traits::{Abs, PowerOf2};
use malachite_q::Rational;
use std::fmt::Write as _;
use the_q::{Dir, MAX_MAG, Q, QI, Rat};

fn rq(r: Rat) -> Rational {
    Rational::from(r.numerator()) / Rational::from(r.denominator())
}

fn show(q: Q) -> String {
    match q {
        Q::Number(r) => format!("{}/{}", r.numerator(), r.denominator()),
        Q::PosSat => "PosSat".into(),
        Q::NegSat => "NegSat".into(),
        Q::PosInf => "PosInf".into(),
        Q::NegInf => "NegInf".into(),
        Q::Nan => "Nan".into(),
    }
}

fn qn(n: i64, d: i64) -> Q {
    Q::Number(Rat::new(n, d).unwrap())
}

struct Lcg(u128);
impl Lcg {
    fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(0x5851_F42D_4C95_7F2D_1405_7B7E_F767_814F)
            .wrapping_add(1);
        (self.0 >> 64) as u64
    }
    fn i64_bits(&mut self, bits: u32) -> i64 {
        let v = (self.next() >> (64 - bits)) as i64;
        if self.next() & 1 == 0 { v } else { -v }
    }
}

#[test]
#[ignore]
fn dump_transcendentals() {
    let mut out = String::new();
    let mut line = |name: &str, input: String, r: Q| {
        writeln!(out, "{name}\t{input}\t{}", show(r)).unwrap();
    };
    // Constants.
    line("pi", "0/1".into(), the_q::transcendental::pi());
    line("e", "0/1".into(), the_q::transcendental::e());
    line("ln2", "0/1".into(), the_q::transcendental::ln2());
    line("half_pi", "0/1".into(), the_q::transcendental::half_pi());

    // exp over [-44, 44] in steps of 1/8, plus tiny arguments.
    for k in -352..=352 {
        let x = qn(k, 8);
        line("exp", format!("{k}/8"), x.exp());
    }
    for k in 1..=40 {
        let d = 1i64 << k;
        line("exp", format!("1/{d}"), qn(1, d).exp());
        line("exp", format!("-1/{d}"), qn(-1, d).exp());
    }
    // ln: log-spaced, near 1, and small.
    for k in 1..=60 {
        let d = 1i64 << k;
        line("ln", format!("{}/{d}", d + 1), qn(d + 1, d).ln());
        line("ln", format!("{}/{d}", d - 1), qn(d - 1, d).ln());
        line("ln", format!("1/{d}"), qn(1, d).ln());
        line("ln", format!("{d}/1"), qn(d, 1).ln());
    }
    for n in 1..=200i64 {
        line("ln", format!("{n}/7"), qn(n, 7).ln());
    }
    // sqrt, cbrt.
    for n in 0..=400i64 {
        line("sqrt", format!("{n}/13"), qn(n, 13).sqrt());
        line("cbrt", format!("{}/13", n - 200), qn(n - 200, 13).cbrt());
    }
    for k in 0..=60 {
        let d = 1i64 << k;
        line("sqrt", format!("{d}/1"), qn(d, 1).sqrt());
        line("sqrt", format!("1/{d}"), qn(1, d).sqrt());
    }
    // sin/cos/tan: dense on [-8, 8], sparse out to the 2^20 limit, and near
    // multiples of pi/2 (via rational approximants of pi).
    for k in -640..=640 {
        line("sin", format!("{k}/80"), qn(k, 80).sin());
        line("cos", format!("{k}/80"), qn(k, 80).cos());
        line("tan", format!("{k}/80"), qn(k, 80).tan());
    }
    for k in 4..=20 {
        let x = 1i64 << k;
        for off in [-3i64, -1, 0, 1, 3] {
            let n = x + off;
            line("sin", format!("{n}/1"), qn(n, 1).sin());
            line("cos", format!("{n}/1"), qn(n, 1).cos());
        }
    }
    // Near pi/2 multiples: 355/113 is pi to 3e-7; 103993/33102 to 2e-10.
    for m in 1..=64i64 {
        line("sin", format!("{}/226", 355 * m), qn(355 * m, 226).sin());
        line("cos", format!("{}/226", 355 * m), qn(355 * m, 226).cos());
        line("tan", format!("{}/226", 355 * m), qn(355 * m, 226).tan());
    }
    // atan / asin / acos / atan2.
    for k in -400..=400 {
        line("atan", format!("{k}/40"), qn(k, 40).atan());
    }
    for k in 0..=40 {
        let x = 1i64 << k;
        line("atan", format!("{x}/1"), qn(x, 1).atan());
        line("atan", format!("-{x}/1"), qn(-x, 1).atan());
    }
    for k in -1000..=1000 {
        line("asin", format!("{k}/1000"), qn(k, 1000).asin());
        line("acos", format!("{k}/1000"), qn(k, 1000).acos());
    }
    for (y, x) in [
        (1, 1),
        (1, -1),
        (-1, 1),
        (-1, -1),
        (0, 1),
        (0, -1),
        (1, 0),
        (-1, 0),
        (3, 4),
        (-3, 4),
        (1000000, 1),
        (1, 1000000),
    ] {
        line("atan2", format!("{y}/1,{x}/1"), qn(y, 1).atan2(qn(x, 1)));
    }
    // Hyperbolics.
    for k in -160..=160 {
        line("sinh", format!("{k}/8"), qn(k, 8).sinh());
        line("cosh", format!("{k}/8"), qn(k, 8).cosh());
        line("tanh", format!("{k}/8"), qn(k, 8).tanh());
    }
    // exp2 / log2 / log10 / powf / pow_i32 / hypot.
    for k in -320..=320 {
        line("exp2", format!("{k}/8"), qn(k, 8).exp2());
    }
    for n in 1..=300i64 {
        line("log2", format!("{n}/7"), qn(n, 7).log2());
        line("log10", format!("{n}/7"), qn(n, 7).log10());
    }
    for (b, e) in [
        (2, 10),
        (3, -5),
        (10, 15),
        (7, 0),
        (1, 100),
        (-2, 3),
        (-2, 4),
        (5, -20),
    ] {
        line("pow_i32", format!("{b}/1,{e}/1"), qn(b, 1).pow_i32(e));
    }
    for (bn, bd, en, ed) in [
        (2, 1, 1, 2),
        (10, 1, 1, 3),
        (3, 2, 5, 2),
        (1, 2, -3, 2),
        (9, 1, -1, 2),
    ] {
        line(
            "powf",
            format!("{bn}/{bd},{en}/{ed}"),
            qn(bn, bd).powf(qn(en, ed)),
        );
    }
    for (a, b) in [(3, 4), (5, 12), (1, 1), (1000000, 1), (0, 0), (0, 7)] {
        line("hypot", format!("{a}/1,{b}/1"), qn(a, 1).hypot(qn(b, 1)));
    }
    // Special-value table.
    line("special:exp(PosInf)", "-".into(), Q::PosInf.exp());
    line("special:exp(NegInf)", "-".into(), Q::NegInf.exp());
    line("special:ln(0)", "-".into(), Q::zero().ln());
    line("special:ln(-1)", "-".into(), qn(-1, 1).ln());
    line("special:sqrt(-1)", "-".into(), qn(-1, 1).sqrt());
    line("special:powf(0,-1)", "-".into(), Q::zero().powf(qn(-1, 1)));
    line("special:powf(0,0)", "-".into(), Q::zero().powf(Q::zero()));
    line("special:powf(0,Nan)", "-".into(), Q::zero().powf(Q::Nan));
    line("special:powf(-8,1/3)", "-".into(), qn(-8, 1).powf(qn(1, 3)));
    line(
        "special:sin(2^20+1)",
        "-".into(),
        qn((1 << 20) + 1, 1).sin(),
    );
    line("special:tan(pi/2 approx)", "-".into(), qn(355, 226).tan());
    line(
        "special:atan2(inf,inf)",
        "-".into(),
        Q::PosInf.atan2(Q::PosInf),
    );
    line("special:atan2(0,0)", "-".into(), Q::zero().atan2(Q::zero()));
    line("special:asin(2)", "-".into(), qn(2, 1).asin());
    line("special:acos(-1)", "-".into(), qn(-1, 1).acos());
    line("special:tanh(PosInf)", "-".into(), Q::PosInf.tanh());
    line("special:cosh(50)", "-".into(), qn(50, 1).cosh());
    line("special:exp(45)", "-".into(), qn(45, 1).exp());
    line("special:exp(-45)", "-".into(), qn(-45, 1).exp());
    line("special:ln(exp(-30))", "-".into(), qn(-30, 1).exp().ln());
    line("special:tanh(50)", "-".into(), qn(50, 1).tanh());
    line("special:tanh(-50)", "-".into(), qn(-50, 1).tanh());
    line("special:tanh(NegInf)", "-".into(), Q::NegInf.tanh());
    line("special:sinh(50)", "-".into(), qn(50, 1).sinh());
    line("special:sinh(-50)", "-".into(), qn(-50, 1).sinh());
    line("special:cosh(-50)", "-".into(), qn(-50, 1).cosh());
    line("special:cosh(PosInf)", "-".into(), Q::PosInf.cosh());
    line("special:exp(42.75)", "-".into(), qn(171, 4).exp());
    line("special:exp(42.5)", "-".into(), qn(85, 2).exp());
    line("special:exp(43)", "-".into(), qn(43, 1).exp());
    line("special:exp2(61)", "-".into(), qn(61, 1).exp2());
    line("special:exp2(62)", "-".into(), qn(62, 1).exp2());
    line("special:pow_i32(2,62)", "-".into(), qn(2, 1).pow_i32(62));
    line("special:sqrt(PosSat)", "-".into(), Q::PosSat.sqrt());
    line("special:ln(PosSat)", "-".into(), Q::PosSat.ln());
    line(
        "special:sqrt(MAX)",
        "-".into(),
        Q::Number(Rat::new(MAX_MAG, 1).unwrap()).sqrt(),
    );
    std::fs::write("target/accuracy-dump.tsv", out).unwrap();
}

/// R3 (directed, 2^-61) and R3+ (nearest, 2^-62) on random operands whose
/// results round, checked against exact malachite arithmetic.
#[test]
fn rounding_bounds_hold() {
    let mut g = Lcg(0x1234_5678_9abc_def0_1122_3344_5566_7788);
    let b61 = Rational::power_of_2(-61i64);
    let b62 = Rational::power_of_2(-62i64);
    let mut rounded = 0usize;
    let mut worst_near = Rational::from(0);
    for _ in 0..100_000 {
        let a =
            Rat::new_rounded(g.i64_bits(62), g.i64_bits(62).abs().max(1), Dir::Nearest).unwrap();
        let b =
            Rat::new_rounded(g.i64_bits(62), g.i64_bits(62).abs().max(1), Dir::Nearest).unwrap();
        let (ra, rb) = (rq(a), rq(b));
        let cases: [(&str, Rational, Rat, Rat, Rat); 4] = [
            (
                "add",
                &ra + &rb,
                Rat::add_dir(a, b, Dir::Down),
                Rat::add(a, b),
                Rat::add_dir(a, b, Dir::Up),
            ),
            (
                "sub",
                &ra - &rb,
                Rat::sub_dir(a, b, Dir::Down),
                Rat::sub(a, b),
                Rat::sub_dir(a, b, Dir::Up),
            ),
            (
                "mul",
                &ra * &rb,
                Rat::mul_dir(a, b, Dir::Down),
                Rat::mul(a, b),
                Rat::mul_dir(a, b, Dir::Up),
            ),
            (
                "div",
                if b.is_zero() {
                    Rational::from(0)
                } else {
                    &ra / &rb
                },
                if b.is_zero() {
                    Rat::zero()
                } else {
                    Rat::div_dir(a, b, Dir::Down)
                },
                if b.is_zero() {
                    Rat::zero()
                } else {
                    Rat::div(a, b)
                },
                if b.is_zero() {
                    Rat::zero()
                } else {
                    Rat::div_dir(a, b, Dir::Up)
                },
            ),
        ];
        for (name, exact, lo, near, hi) in cases {
            if name == "div" && b.is_zero() {
                continue;
            }
            let mag = (&exact).abs();
            if mag > MAX_MAG {
                continue; // saturation region is outside R3 by contract
            }
            let scale = if mag > 1 {
                mag.clone()
            } else {
                Rational::from(1)
            };
            let (vlo, vn, vhi) = (rq(lo), rq(near), rq(hi));
            assert!(
                vlo <= exact && exact <= vhi,
                "R2 {name}: {vlo} <= {exact} <= {vhi}"
            );
            let elo = (&vlo - &exact).abs() / &scale;
            let ehi = (&vhi - &exact).abs() / &scale;
            let en = (&vn - &exact).abs() / &scale;
            assert!(elo <= b61 && ehi <= b61, "R3 {name}: {elo} {ehi}");
            assert!(
                en <= b62,
                "R3+ {name}: nearest error {en} > 2^-62 for {a} op {b}"
            );
            if vn != exact {
                rounded += 1;
                if en > worst_near {
                    worst_near = en;
                }
            }
        }
    }
    let w = worst_near.to_string();
    println!("rounded cases: {rounded}; worst nearest relative error {w}");
    assert!(rounded > 10_000, "sample did not exercise rounding enough");
}

/// The composed weighted_mean bound, 8k·delta_den/(delta_num·2^61).
#[test]
fn weighted_mean_bound_holds() {
    let mut g = Lcg(0xdead_beef_0bad_f00d_1357_9bdf_2468_ace0);
    let mut worst_ratio = Rational::from(0);
    for trial in 0..2_000 {
        let k = 2 + (g.next() % 64) as usize;
        let mut pairs = Vec::new();
        for _ in 0..k {
            // weights and values in [0, 1] with wide denominators
            let d = (g.next() % ((1u64 << 40) - 1) + 1) as i64;
            let w = Rat::new_rounded((g.next() % (d as u64 + 1)) as i64, d, Dir::Nearest).unwrap();
            let d2 = (g.next() % ((1u64 << 40) - 1) + 1) as i64;
            let x =
                Rat::new_rounded((g.next() % (d2 as u64 + 1)) as i64, d2, Dir::Nearest).unwrap();
            pairs.push((w, x));
        }
        let exact_w: Rational = pairs.iter().map(|(w, _)| rq(*w)).sum();
        if exact_w == 0 {
            continue;
        }
        let exact_num: Rational = pairs.iter().map(|(w, x)| rq(*w) * rq(*x)).sum();
        let exact = &exact_num / &exact_w;
        let Some(got) = the_q::nary::weighted_mean(&pairs) else {
            panic!("trial {trial}: weighted_mean returned None with nonzero weights");
        };
        // delta = exact weight sum itself (the tightest admissible lower bound).
        let bound = Rational::from(8 * k as i64) / (&exact_w * Rational::power_of_2(61i64));
        let err = (rq(got) - &exact).abs();
        assert!(err <= bound, "trial {trial}: k={k} err={err} bound={bound}");
        if bound > 0 {
            let ratio = &err / &bound;
            if ratio > worst_ratio {
                worst_ratio = ratio;
            }
        }
    }
    println!("weighted_mean: worst err/bound ratio {worst_ratio}");
}

/// Interval enclosure under rounding, for every sign pattern.
#[test]
fn interval_enclosure_holds() {
    let mut g = Lcg(0x0f0f_1e1e_2d2d_3c3c_4b4b_5a5a_6969_7878);
    for _ in 0..20_000 {
        let mk = |g: &mut Lcg| {
            let a = Rat::new_rounded(g.i64_bits(62), g.i64_bits(62).abs().max(1), Dir::Nearest)
                .unwrap();
            let b = Rat::new_rounded(g.i64_bits(62), g.i64_bits(62).abs().max(1), Dir::Nearest)
                .unwrap();
            if Rat::le(a, b) {
                QI::new(a, b)
            } else {
                QI::new(b, a)
            }
        };
        let (p, q) = (mk(&mut g), mk(&mut g));
        // pick interior points: endpoints and the exact midpoint
        let pts = |i: QI| {
            let (lo, hi) = (rq(i.lower()), rq(i.upper()));
            let mid = (&lo + &hi) / Rational::from(2);
            [lo, mid, hi]
        };
        for x in pts(p) {
            for y in pts(q) {
                let s = QI::add(p, q);
                let d = QI::sub(p, q);
                let m = QI::mul(p, q);
                let ok = |i: QI, v: &Rational| rq(i.lower()) <= *v && *v <= rq(i.upper());
                let (es, ed, em) = (&x + &y, &x - &y, &x * &y);
                // saturation can legitimately clip; only check inside the budget
                let inb = |v: &Rational| v.abs() <= MAX_MAG;
                if inb(&es) {
                    assert!(ok(s, &es), "add enclosure");
                }
                if inb(&ed) {
                    assert!(ok(d, &ed), "sub enclosure");
                }
                if inb(&em) {
                    assert!(ok(m, &em), "mul enclosure");
                }
            }
        }
    }
}
