#!/usr/bin/env python3
import hashlib,json,pathlib,sys
r=pathlib.Path(__file__).resolve().parent
m=json.loads((r/"manifest.json").read_text())
assert m["schema"]=="focused-extractor-proof-packet-v1"
for mod in m["modules"]:
 p=r/mod["source"]; assert p.is_file() and hashlib.sha256(p.read_bytes()).hexdigest()==mod["source_sha256"]
 q=r/mod["receipt"]; d=json.loads(q.read_text()); assert d["exit_status"]==0 and d["object_sha256"]==mod["object_sha256"]
 assert d["source_sha256"]==mod["source_sha256"]==d["source_sha256_after"]
for section in ("direct_import_source_map","selected_transitive_source_owners"):
 for name,owner in m[section].items():
  p=r/owner["source"]; assert p.is_file() and hashlib.sha256(p.read_bytes()).hexdigest()==owner["source_sha256"]
for p in r.rglob("*.olean"): raise AssertionError(f"binary included: {p}")
print("packet checks passed")
