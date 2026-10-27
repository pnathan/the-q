# Releasing

A release is a pushed `vX.Y.Z` tag. Nothing is `cargo publish`ed from a
laptop.

1. **Version-bump PR.** [release-plz](https://release-plz.dev) (config:
   `release-plz.toml`, workflow: `.github/workflows/release-plz.yml`) keeps a
   standing pull request open on every push to `trunk`, titled like
   `chore: release v0.3.0`. It bumps `Cargo.toml`'s `version` and writes
   `CHANGELOG.md` from the [Conventional
   Commits](https://www.conventionalcommits.org/) merged since the version
   on crates.io. It is force-pushed to as new commits land; review it like
   any other PR, and merge it when a release is wanted.
2. **Tag.** On the merged commit:

   ```sh
   git fetch origin trunk && git checkout origin/trunk
   git tag -a v0.3.0 -m v0.3.0      # must equal Cargo.toml's version
   git push origin v0.3.0
   ```

3. **Publish.** `.github/workflows/release.yml` runs on the tag push:
   * `tag` fails fast unless the tag is `v` + `Cargo.toml`'s version and the
     tagged commit is on `trunk`;
   * `ci` runs the whole of `ci.yml` (build, tests, clippy, fmt, MSRV,
     licences, vacuous-theorem lint, `verus verify`) on the tagged commit;
   * `publish` runs `cargo publish --locked` with the `CARGO_REGISTRY_TOKEN`
     repository secret, then creates the GitHub Release with generated notes.

   Re-running a failed `publish` is safe: it skips `cargo publish` when the
   version is already on crates.io and skips the GitHub Release when one
   exists.

release-plz never pushes the tag itself. A tag pushed with a workflow's
`GITHUB_TOKEN` does not trigger other workflows, so a tag it created would
not reach `release.yml`; the tag is pushed by a person.

## Failure modes

* **Tag does not match `Cargo.toml`.** `tag` fails; nothing is published.
  Delete the tag (`git push origin :refs/tags/vX.Y.Z`), fix, re-tag.
* **CI red on the tagged commit.** Nothing is published. Fix on `trunk`
  through a PR, delete the tag, re-tag the fixed commit.
* **Expired or revoked `CARGO_REGISTRY_TOKEN`.** `cargo publish` fails with
  an authentication error. Replace the secret (Settings → Secrets and
  variables → Actions) with a crates.io token scoped `publish-update` for
  `the-q`, then re-run the failed job.
* A version published to crates.io cannot be replaced, only yanked.

## Version discipline

Until told otherwise, `the-q` stays on `0.x.y`. release-plz's default rule
for `0.x` bumps the minor version on a breaking change and the patch version
otherwise; nothing reaches `1.0.0` on its own. For `1.0`, edit `Cargo.toml`'s
`version` by hand in the release PR before merging it.

`semver_check` is off: `gcd`, `model`, `round`, `lipschitz` and `fx` are
exempt from semver (see `CLAUDE.md`, "API stability"), and
`cargo-semver-checks` cannot see that exemption.

## Conventional Commits

Every commit message (on a squash merge, the PR title) needs a
`type(scope)?: description` prefix — `feat`, `fix`, `perf`, `refactor`,
`doc`, `test`, `chore`, `ci`, `build`, `style`, `revert` — since the
changelog groups on it. An unrecognised prefix lands in the changelog
ungrouped rather than failing anything.

## Releasing without the release-plz PR

Bump `Cargo.toml`'s `version` (and `Cargo.lock`), add the `CHANGELOG.md`
entry by hand, merge to `trunk` through a PR, then tag as in step 2.

If a change alters a proven bound, an accuracy figure, or the verified count,
`README.md` and `VERIFICATION.md` still need updating in the same PR — see
`CLAUDE.md`. release-plz only touches `Cargo.toml`, `Cargo.lock` and
`CHANGELOG.md`.
