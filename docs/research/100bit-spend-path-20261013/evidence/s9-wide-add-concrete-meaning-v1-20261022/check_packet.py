#!/usr/bin/env python3
import hashlib,json
from pathlib import Path
r=Path(__file__).resolve().parent;m=json.loads((r/"manifest.json").read_text())
assert m["schema"]=="focused-extractor-proof-packet-v1" and m["lean_exit_status"]==0
assert m["compiled_objects_included"] is False and m["object_in_packet"] is False
for f in m["files"]:
 b=(r/f["path"]).read_bytes();assert len(b)==f["bytes"] and hashlib.sha256(b).hexdigest()==f["sha256"],f["path"]
assert not list(r.rglob("*.olean")) and not list(r.rglob("*.ilean"))
rec=json.loads((r/"evidence/receipt.json").read_text());assert rec["source_sha256"]==m["source_sha256"] and rec["object_sha256"]==m["object_sha256"] and rec["exit_status"]==0
print("PASS: concrete add meaning packet hashes and no-binary policy")
