#!/usr/bin/env python3
import hashlib,json
from pathlib import Path
b=Path(__file__).resolve().parent;m=json.loads((b/"manifest.json").read_text())
assert m["schema"]=="focused-lean-proof-packet-v1" and not m["compiled_objects_included"]
for rel,h in m["files"].items():
 p=b/rel;assert p.is_file(),rel;assert hashlib.sha256(p.read_bytes()).hexdigest()==h,rel
r=json.loads((b/"evidence/receipt.json").read_text());c=json.loads((b/"evidence/closure-summary.json").read_text())
assert r["exit_status"]==0 and not r["watchdog_abort"] and not r["foreign_lean_samples"] and r["process_swaps"]==0
assert c["missing"]==[]
log=(b/"evidence/lean.log").read_text()
for name, axioms in m["declarations"].items(): assert f"'{name}' depends on axioms: {axioms}" in log
for p in b.rglob("*"):
 if p.is_file():assert p.suffix not in {".olean",".ilean",".pyc",".llbc"},p
print("PASS: source/receipt/axiom hashes, closure summary, and object exclusions")
