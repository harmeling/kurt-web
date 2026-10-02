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
python3 "$web_dir/scripts/generate_language.py" "$lang_dir"
python3 "$web_dir/scripts/generate_manifest.py"
# a new cache name whenever the generated files change, so browsers don't keep an old Kurt
python3 - "$web_dir" <<'PY'
import hashlib, re, sys
from pathlib import Path
web = Path(sys.argv[1])
files = [web / 'kurt.py', web / 'language.json', web / 'manifest.json', *sorted((web / 'theories').glob('*.kurt'))]
digest = hashlib.sha256(b''.join(f.read_bytes() for f in files)).hexdigest()[:12]
worker = web / 'service-worker.js'
text = worker.read_text(encoding='utf-8')
worker.write_text(re.sub(r"const CACHE = '[^']*';", f"const CACHE = 'kurt-playground-{digest}';", text, count=1), encoding='utf-8')
PY
python3 "$web_dir/scripts/smoke_test.py"
echo "Synchronized from $lang_dir. Review and commit the changes when ready."
