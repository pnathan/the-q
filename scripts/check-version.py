#!/usr/bin/env python3
"""Version and changelog discipline (CLAUDE.md, "Commits, versions and the
changelog"; docs/RELEASING.md).

  * every commit since the last release is a Conventional Commit, and so is
    the PR title (--title), which becomes the squash commit;
  * once trunk moves past a `vX.Y.Z` tag, Cargo.toml carries the next version,
    bumped by exactly the level the commits since the tag call for;
  * CHANGELOG.md's first version section is that version;
  * a PR (--base) changes CHANGELOG.md;
  * --release (on a tag push): HEAD is tagged `v<version>` and the section is
    dated, not "Unreleased".

Usage: scripts/check-version.py [--base REF] [--title TITLE] [--release]
"""

import argparse
import json
import re
import subprocess
import sys
import urllib.request

TYPES = "feat|fix|perf|refactor|doc|docs|test|chore|ci|build|style|revert"
CONVENTIONAL = re.compile(rf"^({TYPES})(\([a-z0-9_./-]+\))?(!)?: \S")
SECTION = re.compile(r"^## \[(\d+\.\d+\.\d+)\] - (\d{4}-\d{2}-\d{2}|Unreleased)$", re.M)


def git(*args):
    return subprocess.run(["git", *args], check=True, capture_output=True, text=True).stdout


def parse(v):
    return tuple(int(x) for x in v.split("."))


def bump(v, level):
    major, minor, patch = v
    if level == "major":
        return (major + 1, 0, 0)
    if level == "minor":
        return (major, minor + 1, 0)
    return (major, minor, patch + 1)


def show(v):
    return ".".join(map(str, v))


def cargo_version():
    meta = subprocess.run(
        ["cargo", "metadata", "--locked", "--no-deps", "--format-version", "1"],
        check=True, capture_output=True, text=True).stdout
    return json.loads(meta)["packages"][0]["version"]


def last_tag():
    """Highest `vX.Y.Z` tag reachable from HEAD, or None."""
    tags = [t[1:] for t in git("tag", "--merged", "HEAD", "--list", "v*").split()
            if re.fullmatch(r"v\d+\.\d+\.\d+", t)]
    return max(tags, key=parse) if tags else None


def published_max():
    req = urllib.request.Request(
        "https://crates.io/api/v1/crates/the-q",
        headers={"User-Agent": "the-q check-version (github.com/pnathan/the-q)"})
    with urllib.request.urlopen(req, timeout=30) as r:
        return json.load(r)["crate"]["max_version"]


def required_level(base, messages):
    """semver level the Conventional Commits demand, given the base version."""
    breaking = any(CONVENTIONAL.match(m) and CONVENTIONAL.match(m).group(3)
                   or "BREAKING CHANGE:" in m for m in messages)
    feat = any(m.startswith("feat") for m in messages)
    if base[0] == 0:  # 0.x: breaking bumps minor, everything else patch
        return "minor" if breaking else "patch"
    return "major" if breaking else "minor" if feat else "patch"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--base", help="PR base ref; enables per-PR checks")
    ap.add_argument("--title", help="PR title (the future squash commit)")
    ap.add_argument("--release", action="store_true")
    a = ap.parse_args()
    errors = []

    version = cargo_version()
    changelog = open("CHANGELOG.md", encoding="utf-8").read()
    sections = SECTION.findall(changelog)
    if not sections:
        errors.append("CHANGELOG.md has no `## [X.Y.Z] - YYYY-MM-DD|Unreleased` section")
    elif sections[0][0] != version:
        errors.append(f"CHANGELOG.md's first section is {sections[0][0]}, Cargo.toml says {version}")

    tag = last_tag()
    head_tagged = tag is not None and git("rev-list", "-n1", f"v{tag}").strip() == git("rev-parse", "HEAD").strip()

    if a.release:
        if not head_tagged or tag != version:
            errors.append(f"HEAD is not tagged v{version}")
        if sections and sections[0][1] == "Unreleased":
            errors.append(f"CHANGELOG.md section {version} is still `Unreleased`; date it before tagging")
    elif not head_tagged:
        # Messages since the last release: full bodies, so `BREAKING CHANGE:` footers count.
        rng = [f"v{tag}..HEAD"] if tag else ["HEAD"]
        raw = git("log", "--no-merges", "--format=%H%x00%B%x1e", *rng)
        messages = [c.split("\0", 1)[1].strip() for c in raw.split("\x1e") if "\0" in c]
        if a.title:
            messages.append(a.title)
        if tag:
            # Commit-format check only for this cycle: history before the
            # first tag predates the rule.
            for m in messages:
                if not CONVENTIONAL.match(m):
                    errors.append(f"not a Conventional Commit: {m.splitlines()[0]!r}")
            base = parse(tag)
            want = bump(base, required_level(base, messages))
            if parse(version) != want:
                errors.append(f"last release is v{tag}; commits since call for {show(want)}, Cargo.toml says {version}")
        else:
            # No tag yet: crates.io is the only record of what shipped.
            shipped = published_max()
            if parse(version) <= parse(shipped):
                errors.append(f"{version} is already on crates.io (max {shipped}); bump Cargo.toml")

    if a.title and not CONVENTIONAL.match(a.title):
        errors.append(f"PR title is not a Conventional Commit: {a.title!r}")
    if a.base:
        changed = git("diff", "--name-only", f"{a.base}...HEAD").split()
        if "CHANGELOG.md" not in changed:
            errors.append("this PR does not change CHANGELOG.md; add an entry under the current version")

    for e in errors:
        print(f"::error::{e}")
    if not errors:
        print(f"ok: version {version}, last tag {'v' + tag if tag else 'none'}")
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
