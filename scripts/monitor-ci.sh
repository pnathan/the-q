#!/bin/bash
# Monitor CI status for the current branch
# Shows build, test, and Verus verification results

set -e

REPO="${1:-.}"
BRANCH="${2:-$(git -C "$REPO" rev-parse --abbrev-ref HEAD)}"

echo "=== CI Status Monitor ==="
echo "Repository: $REPO"
echo "Branch: $BRANCH"
echo ""

# Check if GitHub CLI is available
if ! command -v gh &> /dev/null; then
    echo "Error: GitHub CLI (gh) not found"
    echo "Install from: https://cli.github.com/"
    exit 1
fi

# Get the latest commit SHA for the branch
SHA=$(git -C "$REPO" rev-parse HEAD)
echo "Latest commit: $SHA"
echo ""

# Try to get PR information
echo "Looking for associated pull requests..."
PRS=$(gh pr list -R "pnathan/the-q" --head "pnathan:$BRANCH" --json number,title,state 2>/dev/null || echo "")

if [ -z "$PRS" ]; then
    echo "No open pull request found for this branch"
else
    echo "$PRS" | head -1
fi

echo ""
echo "=== Recent Commits ==="
git -C "$REPO" log --oneline -5

echo ""
echo "=== CI Check Recommendations ==="
echo ""
echo "Local verification (before pushing):"
echo "  1. cargo build --all"
echo "  2. cargo test --all"
echo "  3. cargo fmt --check"
echo "  4. cargo clippy --all -- -D warnings"
echo "  5. ./scripts/verify-with-verus.sh"
echo ""
echo "View CI results:"
echo "  gh run list -R pnathan/the-q --branch $BRANCH"
echo ""
echo "View PR checks:"
echo "  gh pr view -R pnathan/the-q 1 --json statusCheckRollup"
echo ""
echo "To monitor automatically, use:"
echo "  watch -n 30 './scripts/monitor-ci.sh'"
