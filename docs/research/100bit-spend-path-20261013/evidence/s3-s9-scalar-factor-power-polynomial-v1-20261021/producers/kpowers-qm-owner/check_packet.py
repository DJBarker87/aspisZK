#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,sys
root=Path(__file__).resolve().parent
M=json.loads((root/"manifest.json").read_text())
assert M.get("schema")=="focused-extractor-proof-packet-v1"
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for f in M["files"]:
 p=root/f["path"]; assert p.is_file(),f"missing {p}"; assert sha(p)==f["sha256"],f"hash mismatch {p}"; assert p.stat().st_size==f["size_bytes"]
for mod in M["modules"]:
 s=root/mod["source"]; assert sha(s)==mod["source_sha256"]
 r=root/mod["receipt"]; q=json.loads(r.read_text()); assert q["exit_status"]==0 and q["source_sha256"]==mod["source_sha256"] and q["object_sha256"]==mod["object_sha256"]
 for owner,oh in mod["direct_imports"].items(): assert M["direct_import_source_map"][owner]["object_sha256"]==oh
for name,owner in M["direct_import_source_map"].items():
 p=(root/owner["source"]).resolve(); assert p.is_file(),f"missing owner source {name}: {p}"; assert sha(p)==owner["source_sha256"],f"owner source hash mismatch {name}"
print("PASS",M["packet"],len(M["modules"]),"modules")
