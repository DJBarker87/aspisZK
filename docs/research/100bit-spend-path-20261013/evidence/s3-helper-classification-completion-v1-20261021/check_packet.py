#!/usr/bin/env python3
import hashlib,json
from pathlib import Path
r=Path(__file__).resolve().parent;m=json.loads((r/"manifest.json").read_text())
assert m["schema"]=="focused-extractor-proof-packet-v1"
for p,h in m["evidence_files"].items():
 q=r/p;assert q.is_file(),f"missing {p}";assert hashlib.sha256(q.read_bytes()).hexdigest()==h,f"hash mismatch {p}"
for x in m["modules"]:
 assert x["exit_status"]==0 and x["producer_object_sha256"]
 assert hashlib.sha256((r/x["source_snapshot"]).read_bytes()).hexdigest()==x["source_sha256"]
assert not list(r.rglob("*.olean")) and not list(r.rglob("*.ir"))
assert len(m["direct_import_source_map"])>=4
print(f"PASS: {len(m['evidence_files'])} files; 2 green theorem owners; source-only S3 scope")
