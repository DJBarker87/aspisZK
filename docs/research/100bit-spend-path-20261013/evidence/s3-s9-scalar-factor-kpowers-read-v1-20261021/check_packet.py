#!/usr/bin/env python3
import hashlib,json,sys
from pathlib import Path
root=Path(__file__).resolve().parent
m=json.loads((root/"manifest.json").read_text())
assert m.get("schema")=="focused-extractor-proof-packet-v1"
for f in m["files"]:
 p=root/f["path"]
 assert p.is_file(), f"missing {p}"
 b=p.read_bytes()
 assert len(b)==f["size_bytes"], f"size mismatch {p}"
 assert hashlib.sha256(b).hexdigest()==f["sha256"], f"hash mismatch {p}"
for name,x in m["direct_import_source_map"].items():
 p=root/x["source"]
 assert p.is_file(), f"missing imported source {name}: {p}"
 assert hashlib.sha256(p.read_bytes()).hexdigest()==x["source_sha256"], f"import hash mismatch {name}"
 r=root/x["producer_receipt"]
 assert r.is_file(), f"missing producer receipt {name}: {r}"
 rec=json.loads(r.read_text())
 assert rec.get("object_sha256")==x["object_sha256"], f"object receipt mismatch {name}"
for mod in m["modules"]:
 for k in ("source","receipt","preflight","command","time_log","lean_log"):
  p=root/mod[k]; assert p.is_file(), f"missing module {k}: {p}"
 assert hashlib.sha256((root/mod["source"]).read_bytes()).hexdigest()==mod["source_sha256"]
 assert json.loads((root/mod["receipt"]).read_text()).get("object_sha256")==mod["object_sha256"]
print("PASS",m["packet"])
