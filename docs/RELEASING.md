# Releasing

`the-q` releases itself. Nothing is tagged, changelogged, or `cargo publish`ed
from a laptop.

[release-plz](https://release-plz.dev) (config: `release-plz.toml`) drives the
whole cycle from `.github/workflows/release-plz.yml`, on every push to
`trunk`:

* **`release-plz-pr`** keeps a standing pull request open, titled something
  like `chore: release the-q v0.3.0`, that bumps `Cargo.toml`'s `version` and
  writes `CHANGELOG.md` from the [Conventional
  Commits](https://www.conventionalcommits.org/) merged since the last
  release (`feat: …`, `fix: …`, `perf: …`, …; see the `[changelog]` section of
  `release-plz.toml` for how each prefix is grouped). It is force-pushed to,
  not replaced, as new commits land, so review it like any other PR.
* **`release-plz-release`** only acts when that PR is merged
  (`release_always = false`): it runs `cargo publish`, pushes the matching
  `vX.Y.Z` tag, and creates the GitHub Release.

Both jobs run behind a `verify` job that re-runs `ci.yml`'s build-and-test gate
against the commit on `trunk`, since a merge commit is not guaranteed to be one
`ci.yml` itself validated.

## Version discipline

Until told otherwise, `the-q` stays on `0.x.y`. release-plz's default semver
rule for `0.x` already does the right thing without configuration: a commit
whose type or footer marks a breaking change bumps the minor version, and an
ordinary `feat`/`fix` bumps the patch version — nothing here reaches `1.0.0`
on its own. When the crate is ready for `1.0`, bump `Cargo.toml`'s `version`
to `1.0.0` by hand in the release PR (or a preceding commit) before merging
it; release-plz will not do that step for you.

## Conventional Commits

Every commit message (or, on a squash-merged PR, at least the PR title
release-plz reads for its squash commit) needs a
`type(scope)?: description` prefix — `feat`, `fix`, `perf`, `refactor`,
`doc`, `test`, `chore`, `ci`, `build`, `style`, `revert` — since the
changelog groups on it. An unrecognised prefix lands in the changelog
ungrouped rather than failing the build.

## One-time setup (already done for `the-q`, redo only if it lapses)

`cargo publish` runs authenticated via crates.io Trusted Publishing (OIDC): a
short-lived token is minted per run, and no `CARGO_REGISTRY_TOKEN` secret is
stored in this repository.

1. On crates.io, under the crate's **Settings → Trusted Publishing**, add a
   GitHub publisher naming this repository (`pnathan/the-q`) and the workflow
   file (`release-plz.yml`).
2. Trusted Publishing cannot publish a crate's first-ever version — `the-q`
   already has published versions, so this does not apply here, but it would
   block trusted publishing on a brand-new crate until one manual `cargo
   publish` seeds it.

## Manually cutting a release (bypassing the standing PR)

Not the normal path, but if a release-plz PR needs to be pre-empted: bump
`Cargo.toml`'s `version`, add the `CHANGELOG.md` entry by hand, commit and
merge to `trunk` directly. `release-plz-release` reacts to the version now
differing from what is published on crates.io regardless of which PR carried
the bump.

If a change alters a proven bound, an accuracy figure, or the verified count,
`README.md` and `VERIFICATION.md` still need updating in the same PR that
bumps the version — see `CLAUDE.md`; release-plz only ever touches
`Cargo.toml`, `Cargo.lock`, and `CHANGELOG.md`.
