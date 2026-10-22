#!/usr/bin/env python3
import hashlib,json
from pathlib import Path
root=Path(__file__).resolve().parent
m=json.loads((root/"manifest.json").read_text())
assert m["schema"]=="focused-extractor-proof-packet-v1" and m["lean_exit_status"]==0
assert m["object_in_packet"] is False and m["compiled_objects_included"] is False
for f in m["files"]:
 p=root/f["path"]
 assert p.is_file(), f["path"]
 assert hashlib.sha256(p.read_bytes()).hexdigest()==f["sha256"], f["path"]
 assert p.stat().st_size==f["bytes"], f["path"]
for p in root.rglob("*"):
 if p.is_file(): assert p.suffix not in {".olean",".ilean",".ir",".llbc",".so",".dylib",".dll"},p
log=(root/"proof/lean.log").read_text()
for n in ("actual_cross_wrapping","actual_cm_mul_graph"): assert n in log,n
assert all(x in log for x in ("propext","Classical.choice","Quot.sound"))
print("PASS: actual CM31 cross/graph packet hashes; standard axioms; no compiled objects")
