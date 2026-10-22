#!/usr/bin/env python3
import hashlib,json,sys
from pathlib import Path
p=Path(__file__).resolve().parent
m=json.loads((p/"manifest.json").read_text())
for f in m["files"]:
 q=p/f["path"]
 if not q.is_file(): raise SystemExit(f"missing {q}")
 h=hashlib.sha256(q.read_bytes()).hexdigest()
 if h!=f["sha256"]: raise SystemExit(f"hash mismatch {q}: {h}")
for x in m["modules"]:
 q=p/x["source"]
 if hashlib.sha256(q.read_bytes()).hexdigest()!=x["source_sha256"]: raise SystemExit("module source mismatch")
for name,x in m["direct_import_source_map"].items():
 q=p/x["source"]
 if hashlib.sha256(q.read_bytes()).hexdigest()!=x["source_sha256"]: raise SystemExit(f"dependency source mismatch: {name}")
print("packet checksums: PASS")
