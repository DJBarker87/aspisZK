#!/usr/bin/env python3
import hashlib
import json
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[4]
manifest = json.loads((HERE / "manifest.json").read_text())
errors = []

def check(path_text, expected, label):
    p = Path(path_text)
    if not p.is_absolute():
        p = (HERE / p).resolve()
    if not p.is_file():
        errors.append(f"missing {label}: {p}")
        return
    got = hashlib.sha256(p.read_bytes()).hexdigest()
    if got != expected:
        errors.append(f"hash mismatch {label}: expected {expected}, got {got} ({p})")

for module in manifest["modules"]:
    check(module["source"], module["source_sha256"], module["module"] + " source")
    for key in ("receipt", "preflight", "command", "time_log", "lean_log", "axiom_audit", "audit_source"):
        value = module.get(key)
        if value:
            p = HERE / value
            if not p.is_file():
                errors.append(f"missing {module['module']} {key}: {p}")
    receipt = module.get("receipt")
    if receipt:
        p = HERE / receipt
        if p.exists():
            d = json.loads(p.read_text())
            if d.get("source_sha256") not in (None, module["source_sha256"]):
                errors.append(f"receipt/source mismatch for {module['module']}")
            if d.get("object_sha256") not in (None, module["object_sha256"]):
                errors.append(f"receipt/object mismatch for {module['module']}")

for consumer, imports in manifest["direct_import_source_map"].items():
    for name, info in imports.items():
        check(info["source"], info["source_sha256"], f"{consumer} import {name} source")
        receipt = (HERE / info["producer_receipt"]).resolve()
        if not receipt.is_file():
            errors.append(f"missing producer receipt {consumer}/{name}: {receipt}")

if errors:
    print("FAIL")
    print("\n".join(errors))
    sys.exit(1)
subprocess.run([sys.executable, str(HERE / "check_adapter.py")], check=True)
print("PASS packet source, producer, and evidence checks")
