#!/usr/bin/env python3
import hashlib,json
from pathlib import Path
r=Path(__file__).resolve().parent;m=json.loads((r/"manifest.json").read_text())
assert m["schema"]=="focused-extractor-proof-packet-v1" and not m["compiled_objects_included"]
t=m["targets"][0];assert t["exit_status"]==0 and t["process_swaps"]==0
for f in m["files"]:
 p=r/f["path"];assert p.is_file()
 assert hashlib.sha256(p.read_bytes()).hexdigest()==f["sha256"] and p.stat().st_size==f["bytes"]
for p in r.rglob("*"):
 if p.is_file(): assert p.suffix not in {".olean",".ilean",".ir",".llbc",".so",".dylib",".dll"},p
log=(r/"proof/lean.log").read_text()
for name in ("u64_wrapping_sub_eq_uscalar","wrapping_add_eq_checked","wrapping_sub_eq_checked","wrapping_mul_eq_checked"):
 assert name in log
for ax in ("propext","Classical.choice","Quot.sound"):assert ax in log
print("PASS: square U64 wrapping/checked primitive source-only packet")
