//! The f64 boundary (kept minimal; see TRUSTED.md).
//!
//! `from_f64_dir` goes the bit-decomposition route: the only unverified
//! step is the one-line `external_body` wrapper equating `f64::to_bits`
//! with Verus's own ghost model of it (`f64_to_bits`). Everything after -
//! extracting sign/exponent/mantissa with `/` and `%`, building the exact
//! rational `+-mant * 2^e`, and rounding it to the budget - is verified
//! integer code against the IEEE-754 decode spec below.
//!
//! `to_f64` is the one genuinely trusted function (display/DTO only).

use vstd::prelude::*;
#[allow(unused_imports)]
use vstd::arithmetic::div_mod::*;
#[allow(unused_imports)]
use vstd::arithmetic::power2::*;

#[allow(unused_imports)]
use crate::gcd::*;
#[allow(unused_imports)]
use crate::q::*;
#[allow(unused_imports)]
use crate::round::*;
#[allow(unused_imports)]
use crate::specs::*;

verus! {

// ---------------------------------------------------------------------------
// IEEE-754 binary64 decode (spec level, arithmetic only - no bit ops)
// ---------------------------------------------------------------------------

/// Sign bit set?
pub open spec fn f64_sign_neg(bits: u64) -> bool {
    bits >= 0x8000_0000_0000_0000
}

/// Bits with the sign bit cleared.
pub open spec fn f64_abs_bits(bits: u64) -> u64 {
    if f64_sign_neg(bits) {
        (bits - 0x8000_0000_0000_0000) as u64
    } else {
        bits
    }
}

/// Raw 11-bit exponent field.
pub open spec fn f64_exp_raw(bits: u64) -> u64 {
    f64_abs_bits(bits) / 0x10_0000_0000_0000
}

/// Raw 52-bit fraction field.
pub open spec fn f64_frac(bits: u64) -> u64 {
    f64_abs_bits(bits) % 0x10_0000_0000_0000
}

/// Finite (not NaN, not infinity)?
pub open spec fn f64_finite(bits: u64) -> bool {
    f64_exp_raw(bits) != 0x7FF
}

/// Integer mantissa: implicit leading 1 for normals, none for subnormals.
pub open spec fn f64_mant(bits: u64) -> int {
    if f64_exp_raw(bits) == 0 {
        f64_frac(bits) as int
    } else {
        0x10_0000_0000_0000 + f64_frac(bits) as int
    }
}

/// Binary exponent: value = (-1)^sign * mant * 2^bexp.
pub open spec fn f64_bexp(bits: u64) -> int {
    if f64_exp_raw(bits) == 0 {
        -1074
    } else {
        f64_exp_raw(bits) - 1075
    }
}

/// Exact numerator of the decoded rational (denominator positive).
pub open spec fn f64_num(bits: u64) -> int {
    let m = if f64_bexp(bits) >= 0 {
        f64_mant(bits) * pow2(f64_bexp(bits) as nat)
    } else {
        f64_mant(bits)
    };
    if f64_sign_neg(bits) {
        -m
    } else {
        m
    }
}

/// Exact (positive) denominator of the decoded rational.
pub open spec fn f64_den(bits: u64) -> int {
    if f64_bexp(bits) >= 0 {
        1
    } else {
        pow2((-f64_bexp(bits)) as nat) as int
    }
}

/// Can this f64 be converted? Finite, and (for large values) the integer
/// magnitude must fit the I2 budget.
pub open spec fn f64_conv_ok(bits: u64) -> bool {
    &&& f64_finite(bits)
    &&& (f64_bexp(bits) >= 0 ==> f64_mant(bits) * pow2(f64_bexp(bits) as nat) <= max_mag())
}

// ---------------------------------------------------------------------------
// The single trusted line: std's to_bits agrees with Verus's model of it
// ---------------------------------------------------------------------------

/// TRUSTED (see TRUSTED.md): returns the IEEE-754 bit pattern of `v`.
/// The ensures ties it to Verus's builtin ghost model `f64_to_bits`, so
/// the only assumption is that `f64::to_bits` implements that model -
/// which is the definition of `to_bits` in the Rust reference.
#[verifier::external_body]
fn f64_bits(v: f64) -> (r: u64)
    ensures
        r == f64_to_bits(v),
{
    v.to_bits()
}

// ---------------------------------------------------------------------------
// Verified conversion
// ---------------------------------------------------------------------------

impl Q {
    /// Convert an f64 to `Q` with directed rounding, treating the input as
    /// the *exact* rational its bits denote (every finite f64 is one).
    ///
    /// Returns `None` for NaN / infinity, and for finite values whose
    /// integer magnitude exceeds `2^62 - 1`. The result satisfies the full
    /// rounding contract (R1-R3) against the decoded rational; in
    /// particular values with `|v| <= 2^61`-ish magnitudes and >= 2^-61
    /// granularity convert exactly (R1).
    pub fn from_f64_dir(v: f64, dir: Dir) -> (r: Option<Q>)
        ensures
            r is Some <==> f64_conv_ok(f64_to_bits(v)),
            r is Some ==> {
                let q = r.unwrap();
                let bits = f64_to_bits(v);
                &&& q.inv()
                &&& round_char(q, f64_num(bits), f64_den(bits), dir)
                &&& rounds_to(q, f64_num(bits), f64_den(bits), dir)
            },
    {
        let bits = f64_bits(v);
        let neg = bits >= 0x8000_0000_0000_0000;
        let abs_bits = if neg { bits - 0x8000_0000_0000_0000 } else { bits };
        let exp_raw = abs_bits / 0x10_0000_0000_0000;
        let frac = abs_bits % 0x10_0000_0000_0000;
        proof {
            lemma_remainder_lower(abs_bits as int, 0x10_0000_0000_0000);
            lemma_remainder_upper(abs_bits as int, 0x10_0000_0000_0000);
            assert(exp_raw == f64_exp_raw(bits));
            assert(frac == f64_frac(bits));
            assert(neg == f64_sign_neg(bits));
            assert(exp_raw <= 0x7FF) by (nonlinear_arith)
                requires
                    exp_raw == abs_bits / 0x10_0000_0000_0000,
                    abs_bits < 0x8000_0000_0000_0000;
        }
        if exp_raw == 0x7FF {
            return None;
        }
        let mant: u64 = if exp_raw == 0 { frac } else { 0x10_0000_0000_0000 + frac };
        proof {
            assert(mant as int == f64_mant(bits));
        }
        if exp_raw >= 1075 {
            // Non-negative binary exponent: the value is the integer mant * 2^e.
            let e: u64 = exp_raw - 1075;
            proof {
                assert(f64_bexp(bits) == e as int);
            }
            if e > 62 {
                proof {
                    // mant >= 2^52, so mant * 2^e >= 2^115 > MAX: reject.
                    lemma2_to64();
                    lemma2_to64_rest();
                    if (e as nat) > 63 {
                        lemma_pow2_strictly_increases(63, e as nat);
                    }
                    assert(f64_mant(bits) * pow2(e as nat) > max_mag()) by (nonlinear_arith)
                        requires
                            f64_mant(bits) >= 0x10_0000_0000_0000,
                            pow2(e as nat) >= pow2(63),
                            pow2(63) == 0x8000_0000_0000_0000;
                }
                return None;
            }
            let p = crate::wide::pow2_u128(e as u32);
            proof {
                lemma2_to64();
                lemma2_to64_rest();
                if (e as nat) < 62 {
                    lemma_pow2_strictly_increases(e as nat, 62);
                }
                assert((mant as int) * (p as int) < 0x2000_0000_0000_0000_0000_0000_0000_0000)
                    by (nonlinear_arith)
                    requires
                        mant < 0x20_0000_0000_0000,
                        p as int == pow2(e as nat),
                        pow2(e as nat) <= pow2(62),
                        pow2(62) == 0x4000_0000_0000_0000;
            }
            let prod: u128 = (mant as u128) * p;
            if prod > MAX_MAG as u128 {
                return None;
            }
            proof {
                lemma_gcd_x_one(prod as nat);
                lemma_gcd_x_one(1);
            }
            let r = crate::q::make_canonical(neg, prod, 1);
            match r {
                Some(q) => {
                    proof {
                        assert(f64_num(bits) == if neg { -(prod as int) } else { prod as int });
                        assert(f64_den(bits) == 1);
                        assert(new_fits(f64_num(bits), 1));
                        assert(q.is_frac(f64_num(bits), 1));
                        lemma_round_char_correct(q, f64_num(bits), 1, dir);
                    }
                    Some(q)
                },
                None => {
                    proof {
                        assert(false);
                    }
                    None
                },
            }
        } else {
            // Negative binary exponent: value = +-mant / 2^t.
            let t: u64 = if exp_raw == 0 { 1074 } else { 1075 - exp_raw };
            proof {
                assert(f64_bexp(bits) == -(t as int));
                assert(f64_den(bits) == pow2(t as nat) as int);
                assert(f64_num(bits) == if neg { -(mant as int) } else { mant as int });
                assert(f64_conv_ok(bits));
            }
            if t <= 114 {
                let p2t = crate::wide::pow2_u128(t as u32);
                proof {
                    lemma2_to64();
                    lemma2_to64_rest();
                    lemma_pow2_adds(62, 52);
                    lemma_pow2_adds(62, 63);
                    if (t as nat) < 114 {
                        lemma_pow2_strictly_increases(t as nat, 114);
                    }
                    assert(pow2(114) == pow2(62) * pow2(52));
                    assert(pow2(114) < 0x2000_0000_0000_0000_0000_0000_0000_0000)
                        by (nonlinear_arith)
                        requires
                            pow2(114) == pow2(62) * pow2(52),
                            pow2(62) == 0x4000_0000_0000_0000,
                            pow2(52) == 0x10_0000_0000_0000;
                }
                let q = crate::round::round_frac(neg, mant as u128, p2t, dir);
                proof {
                    assert(signed(neg, mant as int) == f64_num(bits));
                    lemma_round_char_correct(q, f64_num(bits), f64_den(bits), dir);
                }
                Some(q)
            } else {
                // |value| < 2^53 / 2^115 < 2^-61: below the finest grid.
                Some(tiny_result(neg, mant, t, dir, Ghost(bits)))
            }
        }
    }

    /// TRUSTED (see TRUSTED.md): lossy conversion for display / DTO
    /// boundaries ONLY - never fed back into `Q` arithmetic. Uses two
    /// float roundings (i64 -> f64 twice, one division), so the result is
    /// within a few ulp of the true value; covered by differential tests.
    #[verifier::external_body]
    pub fn to_f64(self) -> f64 {
        (self.num as f64) / (self.den as f64)
    }
}

/// Result for magnitudes below the finest grid step 2^-61 (t >= 115):
/// 0 or +-2^-61 depending on the direction.
fn tiny_result(neg: bool, mant: u64, t: u64, dir: Dir, Ghost(bits): Ghost<u64>) -> (q: Q)
    requires
        mant < 0x20_0000_0000_0000,  // 2^53
        115 <= t <= 1074,
        f64_num(bits) == if neg { -(mant as int) } else { mant as int },
        f64_den(bits) == pow2(t as nat) as int,
    ensures
        q.inv(),
        round_char(q, f64_num(bits), f64_den(bits), dir),
        rounds_to(q, f64_num(bits), f64_den(bits), dir),
{
    let ghost en = f64_num(bits);
    let ghost ed = f64_den(bits);
    proof {
        lemma2_to64();
        lemma2_to64_rest();
        lemma_pow2_adds(53, 62);
        lemma_pow2_adds(53, 61);
        lemma_pow2_adds(54, 61);
        lemma_pow2_pos(t as nat);
        lemma_pow2_pos(61);
        if 115 < t {
            lemma_pow2_strictly_increases(115, t as nat);
        }
        // pow2(115) = 2^53 * 2^62, pow2(114) = 2^53 * 2^61, pow2(115) = 2^54 * 2^61
        assert(pow2(115) == pow2(53) * pow2(62));
        assert(pow2(114) == pow2(53) * pow2(61));
        assert(pow2(115) == pow2(54) * pow2(61));
        // the middle-arm guard: |en| <= MAX * ed
        assert(mant as int <= max_mag() * (pow2(t as nat) as int)) by (nonlinear_arith)
            requires
                mant < 0x20_0000_0000_0000,
                pow2(t as nat) >= 1,
                max_mag() == 0x3FFF_FFFF_FFFF_FFFF;
        assert(abs_i(en) == mant as int);
    }
    if mant == 0 {
        // exact zero: 0 / 2^t reduces to 0/1, which fits (R1 arm).
        let q = Q::zero();
        proof {
            assert(q.is_frac(en, ed)) by (nonlinear_arith)
                requires q.num_s() == 0, en == 0;
            assert(new_fits(en, ed) ==> q.is_frac(en, ed));
            // new_fits(0, 2^t) does hold: gcd(0, N) == N, 0/N == 0, N/N == 1.
            lemma_small_mod(0, pow2(t as nat));
            assert(gcd(0, pow2(t as nat)) == gcd(pow2(t as nat), 0));
            lemma_div_of0(pow2(t as nat) as int);
            lemma_div_by_self(pow2(t as nat) as int);
            assert(new_fits(en, ed));
            lemma_round_char_correct(q, en, ed, dir);
        }
        return q;
    }
    proof {
        // Not representable: gcd(mant, 2^t) <= mant < 2^53, so the reduced
        // denominator is at least 2^t / 2^53 >= 2^62 > MAX.
        let g = gcd(mant as nat, pow2(t as nat));
        lemma_gcd_pos(mant as nat, pow2(t as nat));
        lemma_gcd_divides(mant as nat, pow2(t as nat));
        lemma_divides_le(g, mant as nat);
        lemma_div_exact(g, pow2(t as nat));
        let rd = pow2(t as nat) / g;
        assert(rd > max_mag()) by (nonlinear_arith)
            requires
                pow2(t as nat) == g * rd,
                g <= mant as nat,
                mant < 0x20_0000_0000_0000,
                pow2(t as nat) >= pow2(115),
                pow2(115) == pow2(53) * pow2(62),
                pow2(53) == 0x20_0000_0000_0000,
                pow2(62) == 0x4000_0000_0000_0000,
                max_mag() == 0x3FFF_FFFF_FFFF_FFFF;
        assert(!new_fits(en, ed));
        // The scale is 61 (no maximality clause needed at 61).
        assert(mant as int * pow2(61) <= max_mag() * (pow2(t as nat) as int)) by (nonlinear_arith)
            requires
                mant < 0x20_0000_0000_0000,
                pow2(114) == pow2(53) * pow2(61),
                pow2(53) == 0x20_0000_0000_0000,
                pow2(t as nat) >= pow2(115),
                pow2(115) == 2 * pow2(114),
                pow2(61) > 0,
                pow2(114) > 0,
                max_mag() >= 1;
        assert(is_scale(61, mant as int, ed));
    }
    let mdir = match dir {
        Dir::Down => if neg { Dir::Up } else { Dir::Down },
        Dir::Up => if neg { Dir::Down } else { Dir::Up },
        Dir::Nearest => Dir::Nearest,
    };
    proof {
        assert((en < 0) == neg);
        assert(mdir == mag_dir(dir, en < 0));
    }
    let up = matches!(mdir, Dir::Up);
    if !up {
        // floor / nearest of a sub-grid magnitude is 0
        let q = Q::zero();
        proof {
            // mant * 2^61 < 2^114 < 2^t, and doubled still < 2^t.
            assert(2 * (mant as int * pow2(61)) < pow2(t as nat) as int) by (nonlinear_arith)
                requires
                    mant < 0x20_0000_0000_0000,
                    pow2(114) == pow2(53) * pow2(61),
                    pow2(53) == 0x20_0000_0000_0000,
                    pow2(115) == 2 * pow2(114),
                    pow2(t as nat) >= pow2(115),
                    pow2(61) > 0;
            assert(mant as int * pow2(61) >= 0) by (nonlinear_arith)
                requires mant >= 0, pow2(61) > 0;
            assert(is_mag_round(0, 61, mant as int, ed, mdir)) by {
                match mdir {
                    Dir::Down => {
                        assert(0 * ed <= mant as int * pow2(61) < (0 + 1) * ed) by (nonlinear_arith)
                            requires
                                mant as int * pow2(61) >= 0,
                                2 * (mant as int * pow2(61)) < ed,
                                ed > 0;
                    },
                    Dir::Up => {
                        assert(false);
                    },
                    Dir::Nearest => {
                        assert(0 * ed <= mant as int * pow2(61)
                            && 2 * (mant as int * pow2(61) - 0 * ed) < ed) by (nonlinear_arith)
                            requires
                                mant as int * pow2(61) >= 0,
                                2 * (mant as int * pow2(61)) < ed;
                    },
                }
            };
            assert(signed_mag_round(0, 61, en, ed, dir));
            assert(q.num_s() * pow2(61) == (if en < 0 { -0 } else { 0int }) * q.den_s())
                by (nonlinear_arith)
                requires q.num_s() == 0;
            assert(round_char(q, en, ed, dir));
            lemma_round_char_correct(q, en, ed, dir);
        }
        q
    } else {
        // ceil of a positive sub-grid magnitude is one grid step: +-1 / 2^61
        let p61 = crate::wide::pow2_u128(61);
        proof {
            let g1 = gcd(1nat, p61 as nat);
            lemma_gcd_divides(1nat, p61 as nat);
            lemma_divides_le(g1, 1nat);
            assert(g1 == 1);
            assert(pow2(61) == 0x2000_0000_0000_0000);
        }
        let r = crate::q::make_canonical(neg, 1, p61);
        let q = match r {
            Some(q) => q,
            None => {
                proof {
                    assert(false);
                }
                Q::zero()
            },
        };
        proof {
            assert(q.num_s() == if neg { -1int } else { 1int });
            assert(q.den_s() == pow2(61) as int);
            // is_ceil(1, 61, mant, 2^t): 0 < mant * 2^61 <= 2^t.
            assert(0 * ed < mant as int * pow2(61)) by (nonlinear_arith)
                requires mant >= 1, pow2(61) > 0, ed > 0;
            assert(mant as int * pow2(61) <= ed) by (nonlinear_arith)
                requires
                    mant < 0x20_0000_0000_0000,
                    pow2(114) == pow2(53) * pow2(61),
                    pow2(53) == 0x20_0000_0000_0000,
                    pow2(115) == 2 * pow2(114),
                    pow2(t as nat) >= pow2(115),
                    ed == pow2(t as nat),
                    pow2(61) > 0;
            assert(is_mag_round(1, 61, mant as int, ed, mdir)) by {
                assert((1 - 1) * ed < mant as int * pow2(61) <= 1 * ed) by (nonlinear_arith)
                    requires
                        0 * ed < mant as int * pow2(61),
                        mant as int * pow2(61) <= ed;
            };
            assert(signed_mag_round(1, 61, en, ed, dir));
            assert(q.num_s() * pow2(61) == (if en < 0 { -1int } else { 1int }) * q.den_s())
                by (nonlinear_arith)
                requires
                    q.num_s() == if en < 0 { -1int } else { 1int },
                    q.den_s() == pow2(61) as int;
            assert(round_char(q, en, ed, dir));
            lemma_round_char_correct(q, en, ed, dir);
        }
        q
    }
}

} // verus!
