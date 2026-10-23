#!/usr/bin/env python3
import hashlib,json
from pathlib import Path
r=Path(__file__).resolve().parent;m=json.loads((r/"manifest.json").read_text())
assert m["schema"]=="focused-extractor-proof-packet-v1" and not m["compiled_objects_included"]
assert len(m["targets"])==1 and m["targets"][0]["exit_status"]==0 and m["targets"][0]["process_swaps"]==0
assert m["targets"][0]["source_sha256"]=="aad204cf27e99caaa754b0a0da2ef6b8d1c5434ac9c85baa48c869fd4f40c1e3"
for f in m["files"]:
 p=r/f["path"];assert p.is_file(),f["path"]
 assert hashlib.sha256(p.read_bytes()).hexdigest()==f["sha256"],f["path"]
 assert p.stat().st_size==f["bytes"],f["path"]
for p in r.rglob("*"):
 if p.is_file(): assert p.suffix not in {".olean",".ilean",".ir",".llbc",".so",".dylib",".dll"},p
log=(r/"proof/lean.log").read_text()
for n in ("combined_cm_add_maps_to_probe","combined_cm_sub_maps_to_probe","combined_cm_mul_maps_to_probe","combined_by_r_maps_to_probe"):
 assert n in log,n
assert all(x in log for x in ("propext","Classical.choice","Quot.sound"))
print("PASS: Combined square-cut CM operation Result-map source-only packet")
