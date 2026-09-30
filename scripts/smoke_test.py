#!/usr/bin/env python3
"""Cheap checks for the generated browser assets; no browser dependency required."""
import json
import subprocess
import sys
import tempfile
from pathlib import Path

root = Path(__file__).resolve().parents[1]
manifest = json.loads((root / "manifest.json").read_text(encoding="utf-8"))
for folder, files in manifest["proofs"].items():
    for name in files:
        assert (root / "proofs" / folder / name).is_file(), (folder, name)
for name in manifest["theories"]:
    assert (root / "theories" / name).is_file(), name
runtime = (root / "kurt.py").read_text(encoding="utf-8")
assert "version        = '0.9.0'" in runtime
assert "_EMBEDDED_THEORIES: dict[str, str] = {" in runtime
language = json.loads((root / "language.json").read_text(encoding="utf-8"))
assert language["kurtVersion"] == "0.9.0"
for asset in ("kurt-worker.js", "service-worker.js", "site.webmanifest", "icon.svg"):
    assert (root / asset).is_file(), asset
with tempfile.TemporaryDirectory() as tmp:
    proof = Path(tmp) / "proof.kurt"
    proof.write_text("load prop\nuse A implies B\nuse A\nB\n", encoding="utf-8")
    result = subprocess.run([sys.executable, str(root / "kurt.py"), "--no-kurtc", str(proof)], text=True, capture_output=True)
    if result.returncode:
        raise SystemExit(result.stdout + result.stderr)
print("web assets and standalone runtime smoke test passed")
