#!/usr/bin/env python3
"""Fail if any *shipped* dependency carries a copyleft licence.

Reads `cargo metadata --format-version 1 --all-features` on stdin and walks only
the normal (non-dev, non-build) dependency edges from the workspace roots. The
oracle `malachite-q` is LGPL-3.0-only and must stay in [dev-dependencies].
"""

import json
import sys

BANNED = ("GPL-3", "AGPL", "LGPL-3", "SSPL")


def main() -> int:
    meta = json.load(sys.stdin)
    pkgs = {p["id"]: p for p in meta["packages"]}
    root_ids = set(meta["workspace_members"])
    resolve = {n["id"]: n for n in meta["resolve"]["nodes"]}

    seen: set[str] = set()
    stack = list(root_ids)
    while stack:
        pid = stack.pop()
        if pid in seen:
            continue
        seen.add(pid)
        node = resolve.get(pid)
        if node is None:
            continue
        for dep in node.get("deps", []):
            kinds = {d.get("kind") for d in dep.get("dep_kinds", [{"kind": None}])}
            # `None` is cargo's spelling of "a normal dependency".
            if None in kinds:
                stack.append(dep["pkg"])

    bad = []
    for pid in sorted(seen):
        pkg = pkgs.get(pid)
        if pkg is None or pid in root_ids:
            continue
        lic = pkg.get("license") or ""
        if any(b in lic for b in BANNED):
            bad.append((pkg["name"], pkg["version"], lic))

    if bad:
        print("FAIL: copyleft licences in the shipped dependency tree:")
        for name, version, lic in bad:
            print(f"  {name} {version}: {lic}")
        return 1

    shipped = len(seen) - len(root_ids)
    print(f"  ok: {shipped} shipped dependencies, none GPL-3/LGPL-3/AGPL/SSPL")
    return 0


if __name__ == "__main__":
    sys.exit(main())
