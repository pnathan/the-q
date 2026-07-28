#!/usr/bin/env python3
"""Print the download URL of the x86-linux asset of a Verus release.

Reads the GitHub releases API JSON on stdin and writes one URL on stdout.
Used by .github/workflows/ci.yml to install the verifier.
"""

import json
import sys


def main() -> int:
    rel = json.load(sys.stdin)
    assets = rel.get("assets", [])
    candidates = [
        a["browser_download_url"]
        for a in assets
        if "x86-linux" in a["name"] and a["name"].endswith(".zip")
    ]
    if not candidates:
        names = ", ".join(a["name"] for a in assets) or "(none)"
        print(f"no x86-linux .zip asset in release {rel.get('tag_name')}; saw: {names}",
              file=sys.stderr)
        return 1
    print(candidates[0])
    return 0


if __name__ == "__main__":
    sys.exit(main())
