#!/usr/bin/env python3
import hashlib,json
from pathlib import Path
r=Path(__file__).resolve().parent;m=json.loads((r/"manifest.json").read_text())
assert m["schema"]=="focused-extractor-proof-packet-v1" and m["compiled_objects_included"] is False
assert len(m["targets"])==1 and m["targets"][0]["exit_status"]==0 and m["targets"][0]["process_swaps"]==0
assert m["targets"][0]["source_sha256"]=="0c8b824265d0afcb307a6efc3eda1f8d3c6424af99bf5c2a4740ed57300f0c66"
for f in m["files"]:
 p=r/f["path"];assert p.is_file(),f["path"]
 assert hashlib.sha256(p.read_bytes()).hexdigest()==f["sha256"],f["path"]
 assert p.stat().st_size==f["bytes"],f["path"]
for p in r.rglob("*"):
 if p.is_file(): assert p.suffix not in {".olean",".ilean",".ir",".llbc",".so",".dylib",".dll"},p
log=(r/"proof/lean.log").read_text()
assert "actual_square_words" in log and "actual_square_maps_to_selected" in log
assert all(x in log for x in ("propext","Classical.choice","Quot.sound"))
print("PASS: actual CM31 square operation-level result-map source-only packet")
