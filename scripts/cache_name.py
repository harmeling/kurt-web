#!/usr/bin/env python3
"""Set the service worker's cache name from a hash of everything it caches (its `ASSETS`, and the
theories and proofs), so that browsers fetch a changed playground instead of serving the old one
from their cache. Run by `update.sh` and by the Pages workflow right before deploying."""
import hashlib
import re
from pathlib import Path

root = Path(__file__).resolve().parents[1]
worker = root / "service-worker.js"
text = worker.read_text(encoding="utf-8")
assets = re.search(r"const ASSETS = \[(.*?)\];", text, re.S)
assert assets, "no ASSETS in service-worker.js"
names = [n for n in re.findall(r"'([^']*)'", assets.group(1)) if n not in ("./",)]
files = [root / n for n in names] + sorted((root / "theories").glob("*.kurt")) + sorted((root / "proofs").rglob("*.kurt"))
digest = hashlib.sha256()
for f in files:
    digest.update(f.relative_to(root).as_posix().encode() + b"\0" + f.read_bytes())
name = f"kurt-playground-{digest.hexdigest()[:12]}"
worker.write_text(re.sub(r"const CACHE = '[^']*';", f"const CACHE = '{name}';", text, count=1), encoding="utf-8")
print(f"service worker cache: {name}")
