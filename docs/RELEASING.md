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
     packaging, licences, vacuous-theorem lint, `verus verify`) on the
     tagged commit;
   * `publish` (environment `cargo.io`) packages the crate once, attests
     the `.crate` tarball's build provenance, runs `cargo publish --locked`
     with the `CARGO_REGISTRY_TOKEN` secret, checks that crates.io's checksum
     equals the attested tarball's, and creates the GitHub Release with this
     version's `CHANGELOG.md` section as notes and the tarball attached;
   * `smoke` builds a fresh downstream crate depending on `the-q = "=X.Y.Z"`
     from crates.io.

   Re-running a failed `publish` is safe: it skips `cargo publish` when the
   version is already on crates.io and skips the GitHub Release when one
   exists.

To check a downloaded tarball against its attestation:

```sh
gh attestation verify the-q-X.Y.Z.crate --repo pnathan/the-q
```

release-plz never pushes the tag itself. A tag pushed with a workflow's
`GITHUB_TOKEN` does not trigger other workflows, so a tag it created would
not reach `release.yml`; the tag is pushed by a person.

## Checks on every pull request

* `ci.yml` — including `cargo package`, so a packaging error surfaces on the
  PR rather than after a tag is pushed.
* `pr-title.yml` — the PR title is a Conventional Commit, since a squash
  merge makes it the commit the changelog reads.

## Repository settings

These make the workflows load-bearing; without them they are advisory.
`scripts/configure-github.sh` applies all of them and is safe to re-run (it
needs `gh` logged in as a repository admin):

```sh
CARGO_REGISTRY_TOKEN=… scripts/configure-github.sh   # token optional
```

* **Environment `cargo.io`:** deployable only from `v*` tags, the owner as
  required reviewer (each publish waits for one approval click), and
  `CARGO_REGISTRY_TOKEN` as an environment secret. Given the token in its
  environment, the script moves it there and deletes the repository-level
  copy.
* **Ruleset `trunk`:** PR required; `cargo build + test`, `MSRV (Rust
  1.85)`, `no copyleft in the shipped tree`, `verus verify` and
  `Conventional Commit title` required; no force-push or deletion.
* **Ruleset `release tags`:** `v*` tags cannot be created, moved or deleted
  except by an admin.

Admins bypass both rulesets. release-plz opens its PR with `GITHUB_TOKEN`,
and GitHub starts no workflows for a PR opened that way, so its required
checks never report: merge the release PR with the admin bypass. Its content
is only `Cargo.toml`, `Cargo.lock` and `CHANGELOG.md`, and the tag push
re-runs all of CI before anything is published.

Not scripted: the crates.io side. Use a token scoped `publish-update` on
`the-q` only, with an expiry. Trusted Publishing (OIDC) would remove the
stored secret entirely; switching is a change to the `cargo publish` step.

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
