#!/usr/bin/env python3
import hashlib,json
from pathlib import Path
r=Path(__file__).resolve().parent;m=json.loads((r/"manifest.json").read_text())
assert m["schema"]=="focused-extractor-proof-packet-v1" and m["compiled_objects_included"] is False
assert len(m["targets"])==1 and m["targets"][0]["exit_status"]==0 and m["targets"][0]["process_swaps"]==0
assert m["targets"][0]["source_sha256"]=="118566e6670b0d7b3dfedc25df330def25d9e2e0113b65ce2096534483ab1fb9"
for f in m["files"]:
 p=r/f["path"];assert p.is_file(),f["path"]
 assert hashlib.sha256(p.read_bytes()).hexdigest()==f["sha256"],f["path"]
 assert p.stat().st_size==f["bytes"],f["path"]
for p in r.rglob("*"):
 if p.is_file(): assert p.suffix not in {".olean",".ilean",".ir",".llbc",".so",".dylib",".dll"},p
log=(r/"proof/lean.log").read_text()
assert "actual_qm_mul_maps_to_concrete_helper" in log
assert all(x in log for x in ("propext","Classical.choice","Quot.sound"))
print("PASS: actual QM31-to-installed-helper source-only bridge packet")
