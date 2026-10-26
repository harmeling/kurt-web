#!/usr/bin/env bash
set -euo pipefail

# the playground from a release of Kurt (its tag: the public repository harmeling/kurt-lang at
# that tag), or from a Kurt checkout (a directory; default ../kurt-lang-dev, where Kurt is developed):
#
#     ./update.sh v0.8.1          # a release -- what the workflow sync.yml does
#     ./update.sh ../kurt-lang-dev  # a checkout, e.g. to try what isn't released yet
web_dir=$(cd "$(dirname "$0")" && pwd)
source=${1:-../kurt-lang-dev}
if [[ "$source" =~ ^v[0-9] ]]; then
    tmp=$(mktemp -d)
    trap 'rm -rf "$tmp"' EXIT
    git -c advice.detachedHead=false clone -q --depth 1 --branch "$source" https://github.com/harmeling/kurt-lang.git "$tmp/kurt-lang"
    lang_dir="$tmp/kurt-lang"
else
    lang_dir=$source
fi

python3 "$lang_dir/scripts/build_standalone.py" -o "$web_dir/kurt.py"
rm -rf "$web_dir/tutorial" "$web_dir/keywords" "$web_dir/proofs" "$web_dir/exercises"
rm -f "$web_dir"/theories/*.kurt
mkdir -p "$web_dir/theories" "$web_dir/tutorial" "$web_dir/keywords" "$web_dir/proofs/mafi1"     # (the layout of Kurt's repository: readable links, `#file=tutorial/02-...`)
cp "$lang_dir"/src/kurt/theories/*.kurt "$web_dir/theories/"
cp "$lang_dir"/tutorial/*.kurt "$web_dir/tutorial/"
cp "$lang_dir"/keywords/*.kurt "$web_dir/keywords/"
cp "$lang_dir"/proofs/mafi1/*.kurt "$web_dir/proofs/mafi1/"     # the course "Mathematik für Informatik 1"
# the exercises, each topic with its scene in theory/ (loaded as `load theory/NAME`)
if [ -d "$lang_dir/exercises" ]; then
    for topic in "$lang_dir"/exercises/*/; do
        name=$(basename "$topic")
        mkdir -p "$web_dir/exercises/$name/theory"
        cp "$topic"*.kurt "$web_dir/exercises/$name/"
        cp "$topic"theory/*.kurt "$web_dir/exercises/$name/theory/"
    done
fi
# the reference (doc/kurt-doc.md as a website, MkDocs with the Material theme) in reference/, by that
# Kurt's own script; a Kurt without it (0.10 and older) keeps reference/ as it is. PYTHON: a Python with
# mkdocs-material (e.g. a venv's); SKIP_REFERENCE=1: not built.
python=${PYTHON:-python3}
if [ ! -f "$lang_dir/scripts/build_reference_site.py" ]; then
    echo "The reference: skipped, $source has no scripts/build_reference_site.py"
elif [ -n "${SKIP_REFERENCE:-}" ]; then
    echo "The reference: skipped (SKIP_REFERENCE)"
elif ! "$python" -c 'import mkdocs, material' 2>/dev/null; then
    echo "The reference needs mkdocs-material: pip install mkdocs-material (or PYTHON=..., or SKIP_REFERENCE=1)" >&2
    exit 1
else
    reference_tmp=$(mktemp -d)
    "$python" "$lang_dir/scripts/build_reference_site.py" --out "$reference_tmp/reference" --strict
    rm -rf "$web_dir/reference"
    mv "$reference_tmp/reference" "$web_dir/reference"
    rm -rf "$reference_tmp"
fi
python3 "$web_dir/scripts/generate_language.py" "$lang_dir"
python3 "$web_dir/scripts/generate_manifest.py"
python3 "$web_dir/scripts/cache_name.py"       # a new cache name whenever something it caches changed
python3 "$web_dir/scripts/smoke_test.py"
echo "Synchronized from $source. Review and commit the changes when ready."
