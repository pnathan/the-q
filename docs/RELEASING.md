# Releasing

`trunk` always carries the next version and its changelog; a release is
dating that changelog section and pushing the tag. Nothing is
`cargo publish`ed from a laptop.

## Between releases: every PR

`scripts/check-version.py` (CI job `version and changelog`) and
`.github/workflows/pr-title.yml` enforce:

* **Conventional Commits.** Every commit since the last tag and every PR
  title: `type(scope)?!?: description`, type one of `feat fix perf refactor
  doc docs test chore ci build style revert`. `!` or a `BREAKING CHANGE:`
  footer marks a breaking change. PRs are squash-merged, so the title is
  what lands on `trunk`.
* **The bump.** Once `trunk` moves past `vX.Y.Z`, `Cargo.toml` (and
  `Cargo.lock`) must hold exactly the next version the commits since that
  tag call for:

  | since the tag            | `0.x`  | `1.0` and later |
  |--------------------------|--------|-----------------|
  | any breaking change      | minor  | major           |
  | a `feat`, none breaking  | patch  | minor           |
  | anything else            | patch  | patch           |

  The first PR after a tag makes the bump; a later PR that needs a higher
  level raises it. `1.0.0` is a deliberate edit, never computed.
* **The changelog.** Every PR changes `CHANGELOG.md`, adding its entry under
  the first section, `## [<version>] - Unreleased`, in the matching group.
  That section must name `Cargo.toml`'s version.

Before the first `vX.Y.Z` tag exists, the check compares against the highest
version on crates.io instead and does not inspect old commit messages.

Run it locally before pushing:

```sh
python3 scripts/check-version.py --base origin/trunk --title "fix(round): …"
```

## Cutting a release

1. **Release PR.** Titled `chore: release vX.Y.Z`: replace `Unreleased` in
   the section heading with today's date (`YYYY-MM-DD`) and update the
   dependency lines in `README.md` to `X.Y.Z`. Merge it.
2. **Tag** the merged commit:

   ```sh
   git fetch origin trunk && git checkout origin/trunk
   git tag -a vX.Y.Z -m vX.Y.Z
   git push origin vX.Y.Z
   ```

   The next PR to `trunk` then bumps to the following version and opens a
   new `- Unreleased` section.
3. **Publish.** `.github/workflows/release.yml` runs on the tag push:
   * `tag` fails fast unless the tag is `v` + `Cargo.toml`'s version, its
     `CHANGELOG.md` section is dated, and the tagged commit is on `trunk`;
   * `ci` runs the whole of `ci.yml` (build, tests, clippy, fmt, MSRV,
     packaging, licences, vacuous-theorem lint, `verus verify`) on the
     tagged commit;
   * `publish` (environment `cargo.io`) packages the crate once, attests
     the `.crate` tarball's build provenance, runs `cargo publish --locked`
     with a short-lived Trusted Publishing token (falling back to the
     `CARGO_REGISTRY_TOKEN` secret if the OIDC exchange fails), checks
     that crates.io's checksum equals the attested tarball's, and creates the GitHub Release with this
     version's `CHANGELOG.md` section as notes (no section, no release) and
     the tarball attached;
   * `smoke` builds a fresh downstream crate depending on `the-q = "=X.Y.Z"`
     from crates.io.

   Re-running a failed `publish` is safe: it skips `cargo publish` when the
   version is already on crates.io and skips the GitHub Release when one
   exists.

A tag pushed by a workflow's `GITHUB_TOKEN` starts no workflows; the tag is
pushed by a person.

To check a downloaded tarball against its attestation:

```sh
gh attestation verify the-q-X.Y.Z.crate --repo pnathan/the-q
```

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
  1.85)`, `no copyleft in the shipped tree`, `verus verify`,
  `Conventional Commit title` and `version and changelog` required; no
  force-push or deletion.
* **Ruleset `release tags`:** `v*` tags cannot be created, moved or deleted
  except by an admin.

Admins bypass both rulesets, for recovery only.

Not scripted: the crates.io side. The crate's Trusted Publishing entry names
repository `pnathan/the-q` and workflow `release.yml`. If that entry also
names an environment, it must be `cargo.io`; leave it blank otherwise.
Renaming or splitting `release.yml` breaks publishing until the entry is
updated. `CARGO_REGISTRY_TOKEN` is only the fallback; if kept, scope it
`publish-update` on `the-q` with an expiry.

## Failure modes

* **Tag does not match `Cargo.toml`, or its section is still
  `Unreleased`.** `tag` fails; nothing is published.
  Delete the tag (`git push origin :refs/tags/vX.Y.Z`), fix, re-tag.
* **CI red on the tagged commit.** Nothing is published. Fix on `trunk`
  through a PR, delete the tag, re-tag the fixed commit.
* **Trusted Publishing refused and the fallback token expired.** The
  `crates.io token` step warns and `cargo publish` fails with an
  authentication error. Check the crates.io Trusted Publishing entry (see
  above), or replace the secret with a crates.io token scoped
  `publish-update` for `the-q`; then re-run the failed job.
* **Checksum mismatch after publish.** The version is on crates.io but is not
  the attested tarball (for example, published by hand meanwhile). Yank it
  and release the next patch version.
* **`smoke` fails.** The published crate does not build downstream. Yank it,
  fix, release the next patch version.
* A version published to crates.io cannot be replaced, only yanked.


If a change alters a proven bound, an accuracy figure, or the verified count,
`README.md` and `VERIFICATION.md` still need updating in the same PR; see
`CLAUDE.md`.
