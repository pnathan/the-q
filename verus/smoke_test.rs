// Smoke test for CI's verus install step, deliberately trivial and
// self-contained. Not part of the `the-q` cargo package (nothing under
// src/ declares `mod` for this directory), so it never affects `cargo
// build`/`cargo test`. Run directly by the "verus" CI job:
//   ./verus verus/smoke_test.rs
// If this stops verifying, the toolchain install/invocation is broken, not
// the crate's own proofs -- check this file first.

use vstd::prelude::*;

verus! {

spec fn add1_spec(x: int) -> int {
    x + 1
}

fn add1(x: u32) -> (result: u32)
    requires
        x < u32::MAX,
    ensures
        result as int == add1_spec(x as int),
{
    x + 1
}

fn main() {
    let y = add1(41);
    assert(y == 42);
}

} // verus!
