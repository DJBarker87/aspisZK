#!/usr/bin/env python3
import hashlib, json
from pathlib import Path
root=Path(__file__).resolve().parent
m=json.loads((root/"manifest.json").read_text())
assert m["schema"] == "focused-extractor-proof-packet-v1"
assert m["compiled_objects_included"] is False and m["object_in_packet"] is False
assert m["lean_exit_status"] == 0
assert m["source_sha256"] == m["files"][[f["path"] for f in m["files"]].index("sources/S9QMMulM31PrimitiveSourceBridgeV1.lean")]["sha256"]
for f in m["files"]:
 p=root/f["path"]
 assert p.is_file(), f["path"]
 assert hashlib.sha256(p.read_bytes()).hexdigest()==f["sha256"], f["path"]
 assert p.stat().st_size==f["bytes"], f["path"]
for name in (".olean", ".ilean", ".ir", ".llbc", ".so", ".dylib", ".dll"):
 assert not any(p.is_file() and p.suffix==name for p in root.rglob("*")), name
log=(root/"proof/lean.log").read_text()
for theorem in ("actual_reduce_eq_scalar", "actual_m31_mul_eq_scalar", "actual_m31_add_eq_r22_wrapping", "actual_m31_sub_eq_r22_wrapping", "actual_m31_add_eq_checked", "actual_m31_sub_eq_checked"):
 assert theorem in log, theorem
assert "propext" in log and "Classical.choice" in log and "Quot.sound" in log
print("PASS: S9 actual M31 primitive source bridge; source/evidence hashes valid; standard axioms recorded; no compiled objects")
