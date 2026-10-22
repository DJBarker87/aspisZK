#!/usr/bin/env python3
import hashlib,json
from pathlib import Path
root=Path(__file__).resolve().parent
m=json.loads((root/"manifest.json").read_text())
assert m["schema"]=="focused-extractor-proof-packet-v1"
assert m["compiled_objects_included"] is False
assert m["lean_exit_status"]==0
for f in m["files"]:
 p=root/f["path"]
 assert p.is_file(), f["path"]
 assert hashlib.sha256(p.read_bytes()).hexdigest()==f["sha256"], f["path"]
 assert p.stat().st_size==f["bytes"], f["path"]
for p in root.rglob("*"):
 if p.is_file():
  assert p.suffix not in {".olean", ".ilean", ".ir", ".so", ".dylib", ".dll"}, str(p)
print("PASS: focused CM source map packet; all receipt/source hashes valid; no compiled objects")
