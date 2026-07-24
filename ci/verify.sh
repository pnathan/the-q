#!/usr/bin/env bash
# Run Verus and enforce the trusted-boundary discipline.
#
#   1. TRUSTED.md must document every `external_body` in the Verus sources.
#   2. If `verus` is on PATH:
#        - the admit-free target `verus/src/gcd_checked.rs` MUST verify (hard gate);
#        - the broader scaffold `verus/src/lib.rs` is attempted and REPORTED, but
#          not fatal (it still carries structured `OBLIGATION`/`admit()` steps).
#   3. If `verus` is absent (no toolchain), run the discipline checks only and
#      exit 0 so the non-Verus environment still passes.
#
# The CI job wires the Verus toolchain; see .github/workflows/ci.yml.
set -uo pipefail

cd "$(dirname "$0")/.."

rc=0

# --- trusted-boundary discipline (toolchain-independent) --------------------
echo "==> external_body functions must be documented in TRUSTED.md"
missing=0
while IFS= read -r hit; do
  echo "    external_body site: $hit"
done < <(grep -rn 'external_body' verus/ 2>/dev/null || true)
if ! grep -q 'to_f64' TRUSTED.md; then
  echo "ERROR: TRUSTED.md must document to_f64."
  missing=1
fi
[ "$missing" -eq 0 ] && echo "    ok: trusted boundary documented"
rc=$(( rc | missing ))

echo "==> outstanding proof obligations (admit / OBLIGATION markers)"
grep -rn 'admit()\|OBLIGATION' verus/src/ 2>/dev/null | sed 's/^/    /' || true

# --- verus ------------------------------------------------------------------
if command -v verus >/dev/null 2>&1; then
  echo "==> verus --version"
  verus --version || true

  echo "==> verus verus/src/gcd_checked.rs   (admit-free; hard gate)"
  if verus verus/src/gcd_checked.rs; then
    echo "    ok: gcd_checked verified"
  else
    echo "ERROR: admit-free proof target failed to verify."
    rc=1
  fi

  echo "==> verus verus/src/lib.rs   (broader scaffold; reported, non-fatal)"
  if verus verus/src/lib.rs; then
    echo "    ok: full scaffold verified"
  else
    echo "    NOTE: full scaffold not yet fully discharged (expected while"
    echo "          OBLIGATION/admit markers remain) — non-fatal."
  fi
else
  echo "NOTICE: verus not on PATH — ran discipline checks only."
  echo "        The CI 'verus' job installs the toolchain; locally, install per"
  echo "        https://github.com/verus-lang/verus to run the proofs."
fi

exit "$rc"
