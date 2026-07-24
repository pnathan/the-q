#!/usr/bin/env bash
# Fails if any LGPL-3.0 crate (malachite-q, the differential-test oracle, in
# particular) is reachable from the release (non-dev) dependency graph.
# malachite-q is LGPL-3.0-only, which is why it was rejected as a runtime
# dependency in the first place (see README "Why not malachite-q") -- it
# must never leak out of [dev-dependencies].
set -euo pipefail

cd "$(dirname "$0")/.."

cargo metadata --format-version=1 --all-features >/tmp/the-q-metadata.json

python3 - <<'PY'
import json
import sys

with open("/tmp/the-q-metadata.json") as f:
    meta = json.load(f)

packages = {p["id"]: p for p in meta["packages"]}
root_ids = meta["resolve"]["root"]
root_ids = [root_ids] if isinstance(root_ids, str) else meta["workspace_members"]

nodes = {n["id"]: n for n in meta["resolve"]["nodes"]}

# BFS over edges whose dep_kinds are ALL "dev" excluded; an edge counts as a
# "release" edge if ANY of its dep_kinds is normal or build.
release_reachable = set()
stack = list(root_ids)
while stack:
    node_id = stack.pop()
    if node_id in release_reachable:
        continue
    release_reachable.add(node_id)
    node = nodes.get(node_id)
    if not node:
        continue
    for dep in node.get("deps", []):
        kinds = {dk.get("kind") for dk in dep.get("dep_kinds", [])}
        # dep_kinds entry with kind None/absent means "normal".
        kinds = {k if k else "normal" for k in kinds}
        if kinds & {"normal", "build"}:
            stack.append(dep["pkg"])

offenders = []
for node_id in release_reachable:
    pkg = packages.get(node_id)
    if not pkg:
        continue
    license = (pkg.get("license") or "").upper()
    if "LGPL-3.0" in license or pkg["name"].startswith("malachite"):
        offenders.append((pkg["name"], pkg["version"], pkg.get("license")))

if offenders:
    print("FAIL: LGPL-3.0 (or malachite-*) crate(s) reachable from the release dependency tree:")
    for name, version, license in offenders:
        print(f"  {name} {version}  license={license}")
    sys.exit(1)

print(f"OK: no LGPL-3.0/malachite-* crate in the release dependency tree ({len(release_reachable)} packages checked).")
PY
