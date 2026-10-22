#!/usr/bin/env python3
import hashlib,json
from pathlib import Path
root=Path(__file__).resolve().parent; m=json.loads((root/"manifest.json").read_text())
assert m["schema"]=="focused-extractor-proof-packet-v1" and m["lean_exit_status"]==0
assert m["packet"]=="s9-u64-scalar-compat-v1-20261022"
assert not m["compiled_objects_included"] and not m["object_in_packet"]
assert not list(root.rglob("*.olean")) and not list(root.rglob("*.ilean"))
for f in m["files"]:
 p=root/f["path"]; b=p.read_bytes(); assert len(b)==f["bytes"] and hashlib.sha256(b).hexdigest()==f["sha256"],f["path"]
r=json.loads((root/"evidence/receipt.json").read_text())
assert r["exit_status"]==0 and r["source_sha256"]==m["source_sha256"] and r["object_sha256"]==m["object_sha256"]
assert hashlib.sha256((root/"sources/S9U64ScalarCompatibilityV1.lean").read_bytes()).hexdigest()==m["source_sha256"]
log=(root/"evidence/lean.log").read_text(); assert all(x in log for x in ["u64_wrapping_add_eq_uscalar","u64_wrapping_mul_eq_uscalar","u64_and_eq_uscalar"])
print("PASS: source-only U64/UScalar compatibility packet, receipt, and theorem axioms pin")
