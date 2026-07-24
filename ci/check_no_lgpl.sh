#!/usr/bin/env bash
# Enforce that the LGPL-3.0 oracle (malachite*) is a DEV-dependency only and
# never enters the release (normal) dependency tree — including with every
# feature enabled. A statically-linked proprietary binary must not pull it in.
set -euo pipefail

cd "$(dirname "$0")/.."

fail=0

# The normal (non-dev) tree, with all features, must contain no malachite crate.
for feat in "--no-default-features" "--all-features"; do
  echo "==> cargo tree -e normal $feat"
  if cargo tree -e normal $feat 2>/dev/null | grep -i 'malachite'; then
    echo "ERROR: malachite (LGPL-3.0) found in the NORMAL dependency tree ($feat)."
    fail=1
  else
    echo "    ok: no LGPL crate in normal tree ($feat)"
  fi
done

# Sanity: it *should* be present in the dev tree (otherwise the oracle isn't wired).
if ! cargo tree -e dev 2>/dev/null | grep -qi 'malachite-q'; then
  echo "ERROR: malachite-q missing from the DEV tree — the oracle harness is not wired."
  fail=1
else
  echo "    ok: malachite-q present in dev tree (oracle wired)"
fi

exit $fail
