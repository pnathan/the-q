#!/usr/bin/env bash
#
# The oracle (malachite-q and friends) is LGPL-3.0-only. That is fine for test
# code that is never distributed, and a blocker for a statically linked
# proprietary binary. This script fails if it — or anything else copyleft — ever
# escapes [dev-dependencies] into the shipped tree.
#
# Usage: scripts/check-no-lgpl.sh
set -euo pipefail

cd "$(dirname "$0")/.."

fail=0

echo "==> Checking the normal (non-dev, non-build) dependency tree"

for features in "" "--all-features"; do
    label="${features:-default features}"
    # --edges normal excludes dev-dependencies and build-dependencies.
    tree="$(cargo tree --edges normal ${features} 2>/dev/null)"
    if grep -qi 'malachite' <<<"${tree}"; then
        echo "FAIL (${label}): malachite is in the shipped dependency tree:"
        grep -i -n 'malachite' <<<"${tree}"
        fail=1
    else
        echo "  ok (${label}): no malachite"
    fi
done

echo "==> Checking licences of every shipped dependency"

cargo metadata --format-version 1 --all-features | python3 scripts/check_licenses.py

if [[ "${fail}" -ne 0 ]]; then
    exit 1
fi

echo "==> All licence checks passed"
