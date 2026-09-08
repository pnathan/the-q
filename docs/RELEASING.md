# Releasing

`the-q` publishes to crates.io from `.github/workflows/release.yml`, triggered
by pushing a tag matching `v[0-9]+.[0-9]+.[0-9]+`. The workflow re-runs the
full build-and-test gate, then publishes using crates.io Trusted Publishing:
a short-lived OIDC token is exchanged for a single-use crates.io token, so no
`CARGO_REGISTRY_TOKEN` secret is stored in this repository.

## One-time setup (already done for `the-q`, redo only if it lapses)

1. On crates.io, under the crate's **Settings → Trusted Publishing**, add a
   GitHub publisher naming this repository (`pnathan/the-q`), the workflow
   file (`release.yml`), and the `release` environment.
2. In the GitHub repository settings, create an environment named `release`.
   Add required reviewers on it if publication should wait for human sign-off.

## Cutting a release

1. Bump `version` in `Cargo.toml`. If the change alters a proven bound, an
   accuracy figure, or the verified count, update `README.md` and
   `VERIFICATION.md` in the same commit — see `CLAUDE.md`.
2. Run the full local gate before tagging: `cargo build --locked
   --all-features`, `cargo test --locked --all-features` (and `--release`),
   `cargo clippy --locked --all-targets --all-features -- -D warnings`,
   `cargo fmt --check`, and `cargo verus verify --locked --all-features --
   --multiple-errors 8`.
3. Commit the version bump, merge it to `main`, then tag the merge commit:
   `git tag vX.Y.Z && git push origin vX.Y.Z`.
4. The `verify` job in `release.yml` rejects a tag whose version does not
   match `Cargo.toml`. The `test` job re-runs CI's build-and-test suite
   against the tagged commit. The `publish` job runs `cargo publish
   --dry-run`, then the real `cargo publish`.

A failed `publish` job leaves nothing published; crates.io accepts each
version exactly once, so re-running the workflow on the same tag after
fixing the cause is safe.
