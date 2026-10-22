#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,sys
p=Path(__file__).resolve().parent
m=json.loads((p/"manifest.json").read_text())
assert m["schema"]=="focused-lean-source-evidence-v1" and m["compiled_objects_included"] is False
expected={x["path"]:x["sha256"] for x in m["files"]}
actual={str(x.relative_to(p)):hashlib.sha256(x.read_bytes()).hexdigest() for x in p.rglob("*") if x.is_file() and x.name!="manifest.json"}
assert expected==actual, (set(expected)-set(actual),set(actual)-set(expected))
r=json.loads((p/"evidence/receipt.json").read_text())
assert r["exit_status"]==0 and r["source_sha256"]==expected["source/S9WideMulM31UpperResultMapV1.lean"]
assert r["object_sha256"] and r["process_swaps"]==0 and r["watchdog_abort"] is None
log=(p/"evidence/lean.log").read_text()
for n in ("bind_mapR","qm_mul_m31_result_map","current_qm_mul_m31_eq_map","wide_mul_m31_result_map"):
 assert f"AspisR1S9WideMulM31UpperResultMapV1.{n}" in log
assert "[propext, Classical.choice, Quot.sound]" in log
print("PASS: pinned source-only evidence, successful receipt, no swaps, four axiom reports")
