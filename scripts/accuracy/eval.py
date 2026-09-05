"""Independent accuracy evaluation of the-q transcendentals with mpmath."""
import sys
from fractions import Fraction
from collections import defaultdict
import mpmath as mp

mp.mp.dps = 120

def frac(s):
    n, d = s.split("/")
    return Fraction(int(n), int(d))

def mpf(fr):
    return mp.mpf(fr.numerator) / mp.mpf(fr.denominator)

def ref(name, ins):
    x = mpf(ins[0]) if ins and ins[0] is not None else None
    y = mpf(ins[1]) if len(ins) > 1 else None
    return {
        "pi": lambda: mp.pi, "e": lambda: mp.e, "ln2": lambda: mp.log(2), "half_pi": lambda: mp.pi / 2,
        "exp": lambda: mp.exp(x), "ln": lambda: mp.log(x), "sqrt": lambda: mp.sqrt(x),
        "cbrt": lambda: mp.sign(x) * mp.cbrt(abs(x)), "sin": lambda: mp.sin(x), "cos": lambda: mp.cos(x),
        "tan": lambda: mp.tan(x), "atan": lambda: mp.atan(x), "asin": lambda: mp.asin(x),
        "acos": lambda: mp.acos(x), "atan2": lambda: mp.atan2(x, y), "sinh": lambda: mp.sinh(x),
        "cosh": lambda: mp.cosh(x), "tanh": lambda: mp.tanh(x), "exp2": lambda: mp.power(2, x),
        "log2": lambda: mp.log(x, 2), "log10": lambda: mp.log10(x),
        "pow_i32": lambda: mp.power(x, y), "powf": lambda: mp.power(x, y),
        "hypot": lambda: mp.hypot(x, y),
    }[name]()

refout = open(sys.argv[1] + ".pyref", "w")
worst = defaultdict(lambda: (0, None))       # relative error
worst_abs = defaultdict(lambda: (0, None))   # absolute error (for R3-style claims)
specials = []
nonfinite = defaultdict(list)

for line in open(sys.argv[1]):
    name, inp, out = line.rstrip("\n").split("\t")
    if name.startswith("special:"):
        specials.append((name, out))
        continue
    ins = [frac(s) for s in inp.split(",")] if inp != "0/1" or name in ("exp","ln","sqrt","cbrt","sin","cos","tan","atan","asin","acos","sinh","cosh","tanh","exp2","log2","log10") else []
    if name in ("pi", "e", "ln2", "half_pi"):
        ins = []
    if "/" not in out:
        nonfinite[name].append((inp, out))
        continue
    got = mpf(frac(out))
    try:
        r = ref(name, ins)
    except (ValueError, ZeroDivisionError):
        nonfinite[name].append((inp, out + " (ref undefined)"))
        continue
    if not mp.isfinite(r):
        nonfinite[name].append((inp, out + " (ref nonfinite)"))
        continue
    refout.write(f"{name}\t{inp}\t{mp.nstr(r, 60)}\n")
    err = abs(got - r)
    rel = err / abs(r) if r != 0 else err
    aerr = err / max(1, abs(r))
    if name in ("sin", "cos", "tan"):
        ax = abs(ins[0])
        b = "|x|<=1" if ax <= 1 else "|x|<=8" if ax <= 8 else "|x|<=2^10" if ax <= 1024 else "|x|<=2^20"
        key = f"{name} {b}"
        if aerr > worst_abs[key][0]:
            worst_abs[key] = (aerr, inp)
        if rel > worst[key][0]:
            worst[key] = (rel, inp)
    if rel > worst[name][0]:
        worst[name] = (rel, inp)
    if aerr > worst_abs[name][0]:
        worst_abs[name] = (aerr, inp)

def lg(v):
    return "exact" if v == 0 else f"2^{mp.nstr(mp.log(v, 2), 5)}"

print(f"{'function':10s} {'worst REL err':>14s}  at input                 {'worst err/max(1,|y|)':>22s}  at input")
for name in sorted(worst):
    r, ri = worst[name]
    a, ai = worst_abs[name]
    print(f"{name:10s} {lg(r):>14s}  {str(ri):24s} {lg(a):>22s}  {ai}")
print("\nnon-finite / undefined results:")
for name, rows in sorted(nonfinite.items()):
    print(f"  {name}: {len(rows)} ->", rows[:6])
print("\nspecial values:")
for n, o in specials:
    print(f"  {n:28s} {o}")

print("\nln near one, relative error by k:")
for line in open(sys.argv[1]):
    name, inp, out = line.rstrip("\n").split("\t")
    if name != "ln" or "/" not in out: continue
    f = frac(inp)
    if f.denominator & (f.denominator - 1): continue
    if abs(f.numerator - f.denominator) != 1: continue
    k = f.denominator.bit_length() - 1
    if k not in (2, 4, 8, 9, 12, 16, 24, 32, 48, 60): continue
    r = mp.log(mpf(f)); got = mpf(frac(out))
    print(f"  k={k:2d} {'1+' if f.numerator > f.denominator else '1-'}2^-k  rel {lg(abs(got-r)/abs(r)):>10s}   abs {lg(abs(got-r))}")
