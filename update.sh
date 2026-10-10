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
rm -rf "$web_dir/proofs/tutorial" "$web_dir/proofs/keywords" "$web_dir/proofs/examples" "$web_dir/proofs/mafi1"
rm -f "$web_dir"/theories/*.kurt
mkdir -p "$web_dir/theories" "$web_dir/proofs/tutorial" "$web_dir/proofs/keywords" "$web_dir/proofs/mafi1"
cp "$lang_dir"/src/kurt/theories/*.kurt "$web_dir/theories/"
cp "$lang_dir"/tutorial/*.kurt "$web_dir/proofs/tutorial/"
cp "$lang_dir"/keywords/*.kurt "$web_dir/proofs/keywords/"
cp "$lang_dir"/proofs/mafi1/*.kurt "$web_dir/proofs/mafi1/"     # the course "Mathematik für Informatik 1"
python3 "$web_dir/scripts/generate_language.py" "$lang_dir"
python3 "$web_dir/scripts/generate_manifest.py"
python3 "$web_dir/scripts/cache_name.py"       # a new cache name whenever something it caches changed
python3 "$web_dir/scripts/smoke_test.py"
echo "Synchronized from $source. Review and commit the changes when ready."
