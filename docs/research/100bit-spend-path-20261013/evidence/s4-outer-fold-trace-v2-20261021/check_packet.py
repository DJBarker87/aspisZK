#!/usr/bin/env python3
from pathlib import Path
import hashlib, json, sys
root=Path(__file__).resolve().parent
manifest=json.loads((root/"manifest.json").read_text())
fail=[]
for row in manifest["files"]:
    path=root/row["path"]
    if not path.is_file(): fail.append(f"missing: {row['path']}"); continue
    data=path.read_bytes()
    if hashlib.sha256(data).hexdigest()!=row["sha256"]: fail.append(f"hash: {row['path']}")
    if len(data)!=row["size_bytes"]: fail.append(f"size: {row['path']}")
for path in root.rglob("*"):
    if path.is_file() and path.suffix in {".olean", ".ilean"}: fail.append(f"binary: {path.relative_to(root)}")
if fail:
    print("\n".join(fail)); sys.exit(1)
print(f"OK: {len(manifest['files'])} source/evidence files; no Lean object files")
