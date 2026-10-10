#!/usr/bin/env python3
"""Generate the static-host file listing consumed by editor.js and app.js."""
import json
from pathlib import Path

root = Path(__file__).resolve().parents[1]
proofs = {}
for directory in sorted((root / "proofs").iterdir()):
    if directory.is_dir():
        files = sorted(path.name for path in directory.glob("*.kurt"))
        if files:
            proofs[directory.name] = files
manifest = {
    "proofs": proofs,
    "theories": sorted(path.name for path in (root / "theories").glob("*.kurt")),
}
(root / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
print(f"wrote manifest.json ({sum(map(len, proofs.values()))} proofs, {len(manifest['theories'])} theories)")
