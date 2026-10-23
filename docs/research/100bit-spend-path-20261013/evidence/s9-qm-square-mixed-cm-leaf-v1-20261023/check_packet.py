#!/usr/bin/env python3
import hashlib,json
from pathlib import Path
b=Path(__file__).resolve().parent;m=json.loads((b/"manifest.json").read_text())
assert m["schema"]=="focused-lean-compile-only-packet-v1" and not m["compiled_objects_included"]
for rel,h in m["files"].items():
 p=b/rel;assert p.is_file(),rel;assert hashlib.sha256(p.read_bytes()).hexdigest()==h,rel
r=json.loads((b/"evidence/receipt.json").read_text())
assert r["exit_status"]==0 and not r["watchdog_abort"] and not r["foreign_lean_samples"] and r["process_swaps"]==0
assert r["source_sha256"]==m["owners"]["source_sha256"] and r["object_sha256"]==m["owners"]["object_sha256"]
assert m["owners"]["missing_dependencies"]==0
log=(b/"evidence/lean.log").read_text()
for theorem in ("m31_add_same","m31_sub_same","field_reduce_u64_same","method_reduce_u64_same","m31_mul_same","m31_double_same","cm_add_map","cm_sub_map","cm_mul_map"):
 assert f"'AspisR1S9QMSquareMixedProductMapV1.{theorem}' depends on axioms: [propext, Classical.choice, Quot.sound]" in log, theorem
for p in b.rglob('*'):
 if p.is_file(): assert p.suffix not in {".olean",".ilean",".pyc",".llbc"},p
print("PASS: source/compile receipt, compact closure, standard-axiom audit, and artifact exclusions")
