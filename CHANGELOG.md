# Changelog

All notable changes to `the-q`. Format: one `## [X.Y.Z] - YYYY-MM-DD`
section per release, newest first; the section for the version on `trunk`
reads `- Unreleased` until it is tagged. Groups: Added, Changed, Fixed,
Performance, Removed, Documentation, CI. Versioning follows
[Semantic Versioning](https://semver.org/) as `0.x`: a breaking change bumps
the minor version, anything else the patch version. See `docs/RELEASING.md`.

## [0.2.2] - 2026-10-28

### CI

- Releases publish from a pushed `vX.Y.Z` tag: the whole CI pipeline,
  Verus included, runs on the tagged commit, then `cargo publish` through
  crates.io Trusted Publishing, a build-provenance attestation of the
  `.crate`, a checksum comparison against crates.io, a GitHub Release with
  this changelog's section as notes, and a downstream smoke build.
- CI runs on pushes to `trunk` (the push trigger named `main`) and on every
  pull request, documentation-only ones included.
- Pull requests must carry Conventional Commit titles and commits, bump the
  version as the commits since the last tag require, and add a changelog
  entry (`scripts/check-version.py`).
- `cargo package` runs in CI.

## [0.2.1] - 2026-09-08

Last release before this changelog; see the git history up to
`docs: illustrate the Exact section with an SVG rat at a banker's lamp (#46)`.
