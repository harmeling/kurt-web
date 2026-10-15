#!/usr/bin/env python3
"""Generate the static-host file listing consumed by editor.js."""
import json
from pathlib import Path

root = Path(__file__).resolve().parents[1]
# the folders of proofs, by their path as in Kurt's repository (`tutorial/`, `keywords/`,
# `proofs/mafi1/`): the menus, in this order, and the links `#file=tutorial/02-...`
folders = {}
for path in ["tutorial", "keywords", *sorted(p.relative_to(root).as_posix() for p in (root / "proofs").iterdir() if p.is_dir())]:
    files = sorted(p.name for p in (root / path).glob("*.kurt")) if (root / path).is_dir() else []
    if files:
        folders[f"{path}/"] = files
# the exercises: a folder per topic, its exercises (the scene, in theory/, is loaded by them)
exercises = {}
if (root / "exercises").is_dir():
    for topic in sorted((root / "exercises").iterdir()):
        files = sorted(path.name for path in topic.glob("*.kurt")) if topic.is_dir() else []
        if files:
            exercises[topic.name] = files
manifest = {
    "folders": folders,
    "exercises": exercises,
    "theories": sorted(path.name for path in (root / "theories").glob("*.kurt")),
}
(root / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
print(f"wrote manifest.json ({sum(map(len, folders.values()))} proofs in {len(folders)} folders, {sum(map(len, exercises.values()))} exercises, {len(manifest['theories'])} theories)")
