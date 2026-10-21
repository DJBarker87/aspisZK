#!/usr/bin/env python3
import hashlib,json
from pathlib import Path
r=Path(__file__).resolve().parent;m=json.loads((r/"manifest.json").read_text())
assert m["schema"]=="focused-extractor-proof-packet-v1" and len(m["modules"])==1
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();mod=m["modules"][0]
assert sha(r/mod["source"])==mod["source_sha256"]
rec=json.loads((r/mod["receipt"]).read_text());assert rec["exit_status"]==0 and rec["source_sha256"]==mod["source_sha256"] and rec["object_sha256"]==mod["object_sha256"]
for name,x in m["direct_import_source_map"].items():
 s=Path(x["source"]);o=Path(x["selected_object_path"]);p=Path(x["producer_record"])
 assert s.is_file() and sha(s)==x["source_sha256"],name+" source mismatch"
 assert o.is_file() and sha(o)==x["object_sha256"],name+" object mismatch"
 assert p.is_file() and sha(p)==x["producer_record_sha256"],name+" producer record mismatch"
for theorem in m["theorems"]:assert theorem in (r/mod["source"]).read_text()
assert all(a in (r/"evidence/lean.log").read_text() for a in m["modules"][0]["axioms"])
print("PASS: source/object/producer pins, receipt, theorem inventory, and axioms log verified")
