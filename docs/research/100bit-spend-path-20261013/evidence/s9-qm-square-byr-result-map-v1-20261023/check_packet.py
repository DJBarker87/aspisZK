#!/usr/bin/env python3
import hashlib,json
from pathlib import Path
r=Path(__file__).resolve().parent;m=json.loads((r/"manifest.json").read_text())
assert m["schema"]=="focused-extractor-proof-packet-v1" and not m["compiled_objects_included"]
assert len(m["targets"])==1 and m["targets"][0]["exit_status"]==0 and m["targets"][0]["process_swaps"]==0
assert m["targets"][0]["source_sha256"]=="4bfaf8841600d01784942ebd96c7304d99365fbc0a6fe934be7cc02ac39b8faf"
for f in m["files"]:
 p=r/f["path"];assert p.is_file(),f["path"]
 assert hashlib.sha256(p.read_bytes()).hexdigest()==f["sha256"],f["path"]
 assert p.stat().st_size==f["bytes"],f["path"]
for p in r.rglob("*"):
 if p.is_file(): assert p.suffix not in {".olean",".ilean",".ir",".llbc",".so",".dylib",".dll"},p
log=(r/"proof/lean.log").read_text()
assert "by_r_maps_to_actual" in log and all(x in log for x in ("propext","Classical.choice","Quot.sound"))
print("PASS: QM square mul_by_r structural Result-map source-only packet")
