// Verus verification scaffold for `the-q` (see ../README.md for status).
//
// Entry point: `verus verus/src/lib.rs`. This is a SEPARATE compilation unit
// from the shipped crate (`../../src/lib.rs`); it mirrors that implementation
// with Verus specs and proofs. It is intentionally not part of the `cargo`
// build so that `cargo build` uses plain rustc with no Verus dependency.
//
// Module map (obligations from the spec, §6):
//   model  — ghost model + invariants I1/I2 (V1), division-free value specs (V3)
//   gcd    — Euclid on u64: correctness + termination (V5)
//   arith  — i128 overflow bounds (V2) + value-correctness contracts (V3)
//   round  — rounding contract R1-R4 (V4)
//   laws   — commutativity always; assoc/distrib on exact path; Ord; involutions (V6)

pub mod model;
pub mod gcd;
pub mod arith;
pub mod round;
pub mod laws;

fn main() {}
