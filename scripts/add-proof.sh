#!/usr/bin/env bash
set -euo pipefail

# Put proof files into the playground without a release of Kurt: copy them from a Kurt checkout
# into the same folder here, check them with the playground's own Kurt (kurt.py, the released
# one -- what runs in the browser), update manifest.json and the cache name, run the smoke test,
# commit, and push `main` (which deploys, after the browser tests).
#
#     scripts/add-proof.sh ../kurt-lang-dev/proofs/mafi1/30-new-topic.kurt [more files ...]
#     scripts/add-proof.sh --dry-run ../kurt-lang-dev/proofs/mafi1/30-new-topic.kurt   # no commit, no push
#
# The files keep their place: `proofs/mafi1/X.kurt` of the checkout becomes `proofs/mafi1/X.kurt`
# here (a folder of `proofs/` is a menu of the playground). The next sync with a release
# (`update.sh`) replaces `proofs/mafi1/` by the release's: so commit the file in the Kurt checkout
# too -- then the release brings it back (the script warns if it isn't committed there).

web_dir=$(cd "$(dirname "$0")/.." && pwd)
dry_run=
if [ "${1:-}" = "--dry-run" ]; then
    dry_run=1
    shift
fi
if [ $# -eq 0 ]; then
    echo "usage: scripts/add-proof.sh [--dry-run] PATH/proofs/FOLDER/FILE.kurt ..." >&2
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

added=()
for source in "$@"; do
    source=$(cd "$(dirname "$source")" && pwd)/$(basename "$source")
    if [ ! -f "$source" ] || [[ "$source" != *.kurt ]]; then
        echo "not a .kurt file: $source" >&2
        exit 1
    fi
    # its place below `proofs/`: `proofs/mafi1/X.kurt`
    if [[ "$source" != */proofs/*/*.kurt ]]; then
        echo "not in a folder of proofs/ (e.g. proofs/mafi1/): $source" >&2
        exit 1
    fi
    relative=proofs/${source##*/proofs/}
    mkdir -p "$(dirname "$relative")"
    cp "$source" "$relative"
    added+=("$relative")

    # committed in its checkout? (else the next sync with a release drops it again)
    checkout=$(git -C "$(dirname "$source")" rev-parse --show-toplevel 2>/dev/null || true)
    if [ -n "$checkout" ]; then
        in_checkout=${source#"$checkout"/}
        if ! git -C "$checkout" ls-files --error-unmatch "$in_checkout" >/dev/null 2>&1 \
                || [ -n "$(git -C "$checkout" status --porcelain -- "$in_checkout")" ]; then
            echo "warning: $in_checkout is not committed in $checkout -- the next release won't bring it back" >&2
        fi
    fi
done

# check each with the playground's Kurt, in its folder (a proof may `load` a sibling, mafi1's `matrices`)
for relative in "${added[@]}"; do
    echo "checking $relative with the playground's Kurt ($(python3 kurt.py --version | head -1))"
    if ! (cd "$(dirname "$relative")" && python3 "$web_dir/kurt.py" --no-kurtc "$(basename "$relative")" > /dev/null); then
        echo "$relative doesn't check with the playground's Kurt -- nothing added" >&2
        for file in "${added[@]}"; do      # (as before: a file that was there back, a new one away)
            git checkout -q -- "$file" 2>/dev/null || rm -f "$file"
        done
        exit 1
    fi
done

python3 scripts/generate_manifest.py
python3 scripts/cache_name.py
python3 scripts/smoke_test.py

if [ -n "$dry_run" ]; then
    echo "dry run: the files are here, checked; nothing committed or pushed (git status shows them)"
    exit 0
fi
git add -- "${added[@]}" manifest.json service-worker.js
git commit -q -m "$(printf '%s\n\n%s' "Proofs from the Kurt checkout, without a release: ${added[*]}" \
    "Checked with the playground's Kurt; scripts/add-proof.sh.")"
git push -q origin main
echo "pushed: $(git log --oneline -1) -- the playground deploys after the browser tests (GitHub Actions: Deploy)"
