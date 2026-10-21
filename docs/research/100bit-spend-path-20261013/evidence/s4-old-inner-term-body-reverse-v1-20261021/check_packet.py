#!/usr/bin/env python3
import hashlib,json,sys
from pathlib import Path
p=Path(__file__).resolve().parent;m=json.loads((p/"manifest.json").read_text())
assert m.get("schema")=="focused-extractor-proof-packet-v1"
for f in m["files"]:
 q=p/f["path"]; assert q.is_file(), f"missing {f['path']}"; b=q.read_bytes(); assert len(b)==f["size_bytes"] and hashlib.sha256(b).hexdigest()==f["sha256"], f"hash/size mismatch {f['path']}"; assert q.suffix not in {".olean",".ilean",".c",".o",".a"}, f"binary artifact {q}"
for x in m["modules"]:
 q=p/x["source"]; assert hashlib.sha256(q.read_bytes()).hexdigest()==x["source_sha256"], x["module"]
 assert len(x["object_sha256"])==64, x["module"]
 assert set(x["axioms"]) <= {"propext","Classical.choice","Quot.sound"}, x["module"]
for n,x in m["direct_import_source_map"].items():
 if x.get("source"):
  q=p/x["source"]; assert hashlib.sha256(q.read_bytes()).hexdigest()==x["source_sha256"], n
 assert x.get("selected_object_sha256") and len(x["selected_object_sha256"])==64, n
print("PASS",m["packet"],len(m["files"]),"files")
