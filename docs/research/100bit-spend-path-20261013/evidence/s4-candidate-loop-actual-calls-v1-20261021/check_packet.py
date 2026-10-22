#!/usr/bin/env python3
import hashlib,json
from pathlib import Path
r=Path(__file__).resolve().parent;m=json.loads((r/"manifest.json").read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert m["schema"]=="focused-extractor-proof-packet-v1" and len(m["modules"])==1
x=m["modules"][0];assert sha(r/x["source"])==x["source_sha256"]
rec=json.loads((r/x["receipt"]).read_text());assert rec["exit_status"]==0 and rec["object_sha256"]==x["object_sha256"] and rec["source_sha256"]==x["source_sha256"]
for name,d in m["direct_import_source_map"].items():
 s=Path(d["source"]);o=Path(d["selected_object_path"]);p=Path(d["producer_record"])
 assert s.is_file() and sha(s)==d["source_sha256"],name+" source mismatch"
 assert o.is_file() and sha(o)==d["object_sha256"],name+" object mismatch"
 assert p.is_file() and sha(p)==d["producer_record_sha256"],name+" record mismatch"
for t in m["theorems"]:assert t in (r/x["source"]).read_text()
assert all(a in (r/"evidence/lean.log").read_text() for a in x["axioms"])
print("PASS: packet source/object/producer pins, receipt, theorem list and axioms")
