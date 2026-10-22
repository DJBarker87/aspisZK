#!/usr/bin/env python3
import hashlib,json
from pathlib import Path
r=Path(__file__).resolve().parent;m=json.loads((r/"manifest.json").read_text())
assert m["schema"]=="focused-extractor-proof-packet-v1" and m["lean_exit_status"]==0
assert m["object_in_packet"] is False and m["compiled_objects_included"] is False
for f in m["files"]:
 p=r/f["path"];assert p.is_file(),f["path"]
 assert hashlib.sha256(p.read_bytes()).hexdigest()==f["sha256"],f["path"]
 assert p.stat().st_size==f["bytes"],f["path"]
for p in r.rglob("*"):
 if p.is_file():assert p.suffix not in {".olean",".ilean",".ir",".llbc",".so",".dylib",".dll"},p
log=(r/"proof/lean.log").read_text()
assert "actual_cm_mul_total_canonical" in log
assert all(x in log for x in ("propext","Classical.choice","Quot.sound"))
print("PASS: actual CM31 total/canonical packet hashes; axioms recorded; no compiled objects")
