#!/usr/bin/env bash
set -euo pipefail

# Take proof files out of the playground without a release of Kurt -- the counterpart of
# add_proof.sh: remove them, update manifest.json and the cache name, run the smoke test, commit,
# and push `main` (which deploys, after the browser tests).
#
#     scripts/rm_proof.sh proofs/mafi1/30-new-topic.kurt [more files ...]
#     scripts/rm_proof.sh --dry-run proofs/mafi1/30-new-topic.kurt     # no commit, no push
#
# A file is named by its place in the playground (`proofs/mafi1/X.kurt`, or the same path in a Kurt
# checkout). Refused: a file that another proof of the playground loads (`load matrices`). The next
# sync with a release (`update.sh`) brings back what the release has: so remove the file in the Kurt
# checkout too (the script warns if it is still there, in KURT_CHECKOUT, default ../kurt-lang-dev).

web_dir=$(cd "$(dirname "$0")/.." && pwd)
checkout=${KURT_CHECKOUT:-$web_dir/../kurt-lang-dev}
checkout=$(cd "$checkout" 2>/dev/null && pwd || echo "$checkout")
dry_run=
if [ "${1:-}" = "--dry-run" ]; then
    dry_run=1
    shift
fi
if [ $# -eq 0 ]; then
    echo "usage: scripts/rm_proof.sh [--dry-run] proofs/FOLDER/FILE.kurt ..." >&2
    exit 2
fi

cd "$web_dir"
if [ -z "$dry_run" ] && [ -n "$(git status --porcelain)" ]; then
    echo "the playground has uncommitted changes -- commit or stash them first" >&2
    exit 1
fi
if [ -z "$dry_run" ] && [ "$(git branch --show-current)" != "main" ]; then
    echo "not on main: the playground deploys from main" >&2
    exit 1
fi

removed=()
for name in "$@"; do
    # its place in the playground: `proofs/FOLDER/X.kurt` (also given as a path of a checkout)
    if [[ "$name" != *proofs/*/*.kurt ]]; then
        echo "not a proof file of a folder of proofs/ (e.g. proofs/mafi1/X.kurt): $name" >&2
        exit 1
    fi
    relative=proofs/${name##*proofs/}
    if ! git ls-files --error-unmatch "$relative" >/dev/null 2>&1; then
        echo "not in the playground: $relative" >&2
        exit 1
    fi
    # loaded by another proof of the playground? (`load matrices` for proofs/mafi1/matrices.kurt)
    base=$(basename "$relative" .kurt)
    users=$(grep -rlE "^\s*load\b.*\b${base}\b" --include='*.kurt' proofs exercises tutorial keywords 2>/dev/null | grep -v "^$relative$" || true)
    if [ -n "$users" ]; then
        echo "$relative is loaded by: $(echo $users) -- not removed" >&2
        exit 1
    fi
    removed+=("$relative")
    if [ -f "$checkout/$relative" ]; then
        echo "warning: $relative is still in $checkout -- the next release brings it back; remove it there too" >&2
    fi
done

git rm -q -- "${removed[@]}"
python3 scripts/generate_manifest.py
python3 scripts/cache_name.py
python3 scripts/smoke_test.py

if [ -n "$dry_run" ]; then
    echo "dry run: removed here; nothing committed or pushed (undo: git reset -q HEAD -- . && git checkout -- .)"
    exit 0
fi
git add -- manifest.json service-worker.js
git commit -q -m "$(printf '%s\n\n%s' "Proofs out of the playground, without a release: ${removed[*]}" "scripts/rm_proof.sh.")"
git push -q origin main
echo "pushed: $(git log --oneline -1) -- the playground deploys after the browser tests (GitHub Actions: Deploy)"
