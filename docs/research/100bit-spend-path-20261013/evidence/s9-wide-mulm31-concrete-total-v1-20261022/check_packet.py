#!/usr/bin/env python3
from pathlib import Path
import hashlib,json
p=Path(__file__).resolve().parent
m=json.loads((p/"manifest.json").read_text())
assert m["schema"]=="focused-lean-source-evidence-v1" and m["compiled_objects_included"] is False
e={x["path"]:x["sha256"] for x in m["files"]}
a={str(x.relative_to(p)):hashlib.sha256(x.read_bytes()).hexdigest() for x in p.rglob("*") if x.is_file() and x.name!="manifest.json"}
assert e==a,(set(e)-set(a),set(a)-set(e))
r=json.loads((p/"evidence/receipt.json").read_text())
assert r["exit_status"]==0 and r["process_swaps"]==0 and r["watchdog_abort"] is None
assert r["source_sha256"]==e["source/S9WideMulM31ConcreteTotalV1.lean"]
log=(p/"evidence/lean.log").read_text()
for n in ("toE_sourceToP6W","fromE_mapWide","concrete_wide_mul_m31_maps_source","concrete_wide_mul_m31_total_exact"): assert f"AspisR1S9WideMulM31ConcreteTotalV1.{n}" in log
assert "Classical.choice" in log and "Quot.sound" in log and "sorryAx" not in log
print("PASS: pinned source-only evidence, successful result, no swap, all four axiom reports")
