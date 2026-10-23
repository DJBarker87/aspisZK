#!/usr/bin/env python3
import hashlib,json
from pathlib import Path
r=Path(__file__).resolve().parent;m=json.loads((r/"manifest.json").read_text())
assert m["schema"]=="focused-extractor-proof-packet-v1" and m["compiled_objects_included"] is False
for t in m["targets"]:
 assert t["exit_status"]==0 and t["process_swaps"]==0
 for p in (r/t["path"]).glob("proof/lean.log"):
  assert p.is_file()
for f in m["files"]:
 p=r/f["path"];assert p.is_file(),f["path"]
 assert hashlib.sha256(p.read_bytes()).hexdigest()==f["sha256"],f["path"]
 assert p.stat().st_size==f["bytes"],f["path"]
for p in r.rglob("*"):
 if p.is_file(): assert p.suffix not in {".olean",".ilean",".ir",".llbc",".so",".dylib",".dll"},p
assert "actual_qm_mul_total_canonical" in (r/"total/proof/lean.log").read_text()
assert all(x in (r/"total/proof/lean.log").read_text() for x in ("propext","Classical.choice","Quot.sound"))
assert "actual_qm_mul_eq_checked" in (r/"checked/proof/lean.log").read_text()
assert "actual_qm_mul_wrapping" in (r/"wrap/proof/lean.log").read_text()
print("PASS: actual QM31 wrapping, checked, and total/canonical source-only packet")
