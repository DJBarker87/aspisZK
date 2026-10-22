#!/usr/bin/env python3
import hashlib
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
m = json.loads((HERE / "manifest.json").read_text())
errors = []

def verify(path, expected, label):
    p = Path(path)
    if not p.is_absolute():
        p = (HERE / p).resolve()
    if not p.is_file():
        errors.append(f"missing {label}: {p}")
        return None
    got = hashlib.sha256(p.read_bytes()).hexdigest()
    if expected is not None and got != expected:
        errors.append(f"hash mismatch {label}: {p} expected {expected}, got {got}")
    return p

for mod in m["modules"]:
    src = verify(mod["source"], mod["source_sha256"], mod["module"] + " source")
    rec = verify(mod["receipt"], None, mod["module"] + " receipt")
    if rec:
        d = json.loads(rec.read_text())
        for key, expected in (("source_sha256", mod["source_sha256"]),
                              ("object_sha256", mod["object_sha256"])):
            if d.get(key) != expected:
                errors.append(f"receipt {key} mismatch for {mod['module']}")
    for k in ("preflight", "time_log", "lean_log"):
        p = HERE / mod[k]
        if not p.is_file():
            errors.append(f"missing {mod['module']} {k}: {p}")

for consumer, imports in m["direct_import_source_map"].items():
    for name, item in imports.items():
        verify(item["source"], item["source_sha256"], f"{consumer} import {name} source")
        receipt = (HERE / item["producer_receipt"]).resolve()
        if not receipt.is_file():
            errors.append(f"missing producer manifest for {consumer} import {name}: {receipt}")

log = (HERE / "evidence/lean.log").read_text()
if "propext" not in log or "Classical.choice" not in log or "Quot.sound" not in log:
    errors.append("axiom audit output does not show expected standard axioms")
if "sorryAx" in log or "propext" not in log:
    errors.append("unexpected axiom marker in Lean audit output")

if errors:
    print("FAIL\n" + "\n".join(errors))
    sys.exit(1)
print("PASS focused P6 trace packet source, producer, receipt, and audit checks")
