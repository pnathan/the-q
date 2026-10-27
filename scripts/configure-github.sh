#!/usr/bin/env bash
#
# Applies the repository settings the release pipeline relies on (see
# docs/RELEASING.md, "Repository settings"). Idempotent: re-running updates
# in place. Needs `gh` authenticated as a repository admin.
#
#   * environment `cargo.io` (used by release.yml's publish job):
#     deployable only from `v*` tags, the owner as
#     required reviewer, and CARGO_REGISTRY_TOKEN as an environment secret;
#   * ruleset "trunk": PR required, the CI checks required, no force-push or
#     deletion;
#   * ruleset "release tags": `v*` tags cannot be created, moved or deleted
#     except by an admin.
#
# Admins bypass both rulesets, for recovery (re-pointing a bad tag, an
# emergency fix); normal changes go through PRs.
#
# Usage: scripts/configure-github.sh [owner/repo]
#   CARGO_REGISTRY_TOKEN=… scripts/configure-github.sh   # also moves the token
set -euo pipefail

repo="${1:-pnathan/the-q}"
env_name="cargo.io"
admin_bypass='[{"actor_id": 5, "actor_type": "RepositoryRole", "bypass_mode": "always"}]'

owner_id="$(gh api "repos/$repo" --jq .owner.id)"

echo "==> environment $env_name"
gh api -X PUT "repos/$repo/environments/$env_name" --input - <<JSON >/dev/null
{
  "reviewers": [{"type": "User", "id": $owner_id}],
  "deployment_branch_policy": {"protected_branches": false, "custom_branch_policies": true}
}
JSON
if ! gh api "repos/$repo/environments/$env_name/deployment-branch-policies" \
     --jq '.branch_policies[] | select(.type == "tag" and .name == "v*") | .id' | grep -q .; then
    gh api -X POST "repos/$repo/environments/$env_name/deployment-branch-policies" \
        -f name='v*' -f type=tag >/dev/null
fi

if [ -n "${CARGO_REGISTRY_TOKEN:-}" ]; then
    echo "==> CARGO_REGISTRY_TOKEN -> environment secret; repository secret removed"
    printf '%s' "$CARGO_REGISTRY_TOKEN" |
        gh secret set CARGO_REGISTRY_TOKEN --repo "$repo" --env "$env_name"
    gh secret delete CARGO_REGISTRY_TOKEN --repo "$repo" 2>/dev/null || true
else
    echo "    CARGO_REGISTRY_TOKEN not set in this shell; the repository secret stays as is"
fi

# Create or update a ruleset by name.
put_ruleset() {
    local name="$1" body="$2" id
    id="$(gh api "repos/$repo/rulesets" --jq ".[] | select(.name == \"$name\") | .id")"
    echo "==> ruleset $name"
    if [ -n "$id" ]; then
        gh api -X PUT "repos/$repo/rulesets/$id" --input - <<<"$body" >/dev/null
    else
        gh api -X POST "repos/$repo/rulesets" --input - <<<"$body" >/dev/null
    fi
}

# Check names are the jobs' `name:` fields in ci.yml and pr-title.yml.
put_ruleset trunk "$(cat <<JSON
{
  "name": "trunk",
  "target": "branch",
  "enforcement": "active",
  "bypass_actors": $admin_bypass,
  "conditions": {"ref_name": {"include": ["~DEFAULT_BRANCH"], "exclude": []}},
  "rules": [
    {"type": "deletion"},
    {"type": "non_fast_forward"},
    {"type": "pull_request", "parameters": {
      "required_approving_review_count": 0,
      "dismiss_stale_reviews_on_push": false,
      "require_code_owner_review": false,
      "require_last_push_approval": false,
      "required_review_thread_resolution": false}},
    {"type": "required_status_checks", "parameters": {
      "strict_required_status_checks_policy": false,
      "required_status_checks": [
        {"context": "cargo build + test"},
        {"context": "MSRV (Rust 1.85)"},
        {"context": "no copyleft in the shipped tree"},
        {"context": "verus verify"},
        {"context": "Conventional Commit title"},
        {"context": "version and changelog"}]}}
  ]
}
JSON
)"

put_ruleset "release tags" "$(cat <<JSON
{
  "name": "release tags",
  "target": "tag",
  "enforcement": "active",
  "bypass_actors": $admin_bypass,
  "conditions": {"ref_name": {"include": ["refs/tags/v*"], "exclude": []}},
  "rules": [{"type": "creation"}, {"type": "update"}, {"type": "deletion"}]
}
JSON
)"

echo "done: https://github.com/$repo/settings/rules"
