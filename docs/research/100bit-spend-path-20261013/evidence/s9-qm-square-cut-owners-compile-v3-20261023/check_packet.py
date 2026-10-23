#!/usr/bin/env python3
import hashlib,json
from pathlib import Path
b=Path(__file__).resolve().parent;m=json.loads((b/"manifest.json").read_text())
assert m["schema"]=="focused-lean-compile-only-packet-v1" and not m["compiled_objects_included"]
for rel,h in m["files"].items():
 p=b/rel;assert p.is_file(),rel;assert hashlib.sha256(p.read_bytes()).hexdigest()==h,rel
for n in ("types","funs"):
 e=b/n/"evidence";r=json.loads((e/"receipt.json").read_text());c=json.loads((e/"closure-summary.json").read_text())
 assert r["exit_status"]==0 and not r["watchdog_abort"] and not r["foreign_lean_samples"] and r["process_swaps"]==0
 assert c["missing_count"]==0 and c["missing"]==[]
for p in b.rglob("*"):
 if p.is_file():assert p.suffix not in {".olean",".ilean",".pyc",".llbc"},p
print("PASS: compile receipts, source hashes, summarized closures, and artifact exclusions")
