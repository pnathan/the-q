#!/usr/bin/env bash
set -euo pipefail

repo_dir=$(cd "$(dirname "$0")/.." && pwd)
probe_dir=$(mktemp -d /tmp/the-q-privacy.XXXXXX)
trap 'rm -rf "$probe_dir"' EXIT

cargo build --manifest-path "$repo_dir/Cargo.toml" --locked --target-dir "$probe_dir/target"
rlib=$(find "$probe_dir/target/debug/deps" -maxdepth 1 -name 'libthe_q-*.rlib' -print -quit)
test -n "$rlib"

cat >"$probe_dir/probe.rs" <<'RS'
use the_q::{QI, Rat};

fn main() {
    let mut r = Rat::one();
    r.den = 0;
    let _ = QI { lo: Rat::zero(), hi: Rat::one() };
    let mut i = QI::exact(Rat::zero());
    i.lo = Rat::one();
}
RS

if rustc --edition=2024 --extern "the_q=$rlib" \
    -L "dependency=$probe_dir/target/debug/deps" \
    "$probe_dir/probe.rs" 2>"$probe_dir/error"; then
    echo "error: downstream Rat field mutation compiled" >&2
    exit 1
fi

if ! grep -q 'field `den` of struct `Rat` is private' "$probe_dir/error"; then
    cat "$probe_dir/error" >&2
    exit 1
fi
if ! grep -q 'field `lo` of struct `QI` is private' "$probe_dir/error"; then
    cat "$probe_dir/error" >&2
    exit 1
fi
echo "ok: downstream Rat and QI field access is rejected"
