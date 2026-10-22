#!/usr/bin/env python3
import hashlib
import json
from pathlib import Path

root = Path(__file__).resolve().parent
manifest = json.loads((root / "manifest.json").read_text())
errors = []
for entry in manifest["files"]:
    path = root / entry["path"]
    if not path.is_file():
        errors.append(f"missing: {entry['path']}")
        continue
    digest = hashlib.sha256(path.read_bytes()).hexdigest()
    if digest != entry["sha256"]:
        errors.append(f"hash mismatch: {entry['path']}")
for path in root.rglob("*"):
    if not path.is_file() or path.name in {"manifest.json", "check_packet.py"}:
        continue
    if path.suffix in {".olean", ".ilean", ".pyc", ".llbc", ".exe", ".o", ".a", ".so", ".dylib"} or "__pycache__" in path.parts:
        errors.append(f"forbidden generated artifact: {path.relative_to(root)}")
if errors:
    raise SystemExit("FAIL\n" + "\n".join(errors))
print(f"PASS {len(manifest['files'])} manifested source/evidence files; no compiled objects or caches")
