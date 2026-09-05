# Accuracy audit

Two independent oracles for the transcendental functions: `eval.py` (mpmath,
120 digits) and `eval.lisp` (SBCL, exact rational series on a `2^-160` grid).
They share nothing with the crate or with each other, and the Lisp run also
reports how far the two oracles disagree.

```sh
cargo test --release --test bounds dump_transcendentals -- --ignored
python3 scripts/accuracy/eval.py target/accuracy-dump.tsv
sbcl --script scripts/accuracy/eval.lisp target/accuracy-dump.tsv
```
