#!/usr/bin/env bash
set -euo pipefail

lang_dir=${1:-../kurt-lang}
web_dir=$(cd "$(dirname "$0")" && pwd)

python3 "$lang_dir/scripts/build_standalone.py" -o "$web_dir/kurt.py"
mkdir -p "$web_dir/theories" "$web_dir/proofs/tutorial" "$web_dir/proofs/examples"
cp "$lang_dir"/src/kurt/theories/*.kurt "$web_dir/theories/"
cp "$lang_dir"/tutorial/*.kurt "$web_dir/proofs/tutorial/"
cp "$lang_dir/proofs/natural-deduction/contraposition.kurt" \
   "$lang_dir/proofs/natural-deduction/double-negation.kurt" \
   "$lang_dir/proofs/natural-deduction/de-morgan.kurt" \
   "$lang_dir/proofs/natural-deduction/excluded-middle.kurt" \
   "$lang_dir/modus-ponens.kurt" \
   "$lang_dir/proofs/natural-deduction/proof-by-contradiction.kurt" \
   "$web_dir/proofs/examples/"
python3 "$web_dir/scripts/generate_manifest.py"
python3 "$web_dir/scripts/smoke_test.py"
echo "Synchronized from $lang_dir. Review and commit the changes when ready."
