#!/usr/bin/env python3
import hashlib, json
from pathlib import Path
ROOT = Path(__file__).resolve().parents[5]
PACKET = Path(__file__).resolve().parent
M = json.loads((PACKET / "manifest.json").read_text())
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
errors=[]
for rel,digest in M["evidence_files"].items():
    q=PACKET/rel
    if not q.is_file() or sha(q)!=digest: errors.append(f"evidence mismatch: {rel}")
for mod in M["modules"]:
    q=PACKET/mod["source"]
    if not q.is_file() or sha(q)!=mod["source_sha256"]: errors.append(f"source mismatch: {mod['source']}")
    if mod["receipt_sha256"] != sha(PACKET/mod["receipt"]): errors.append(f"receipt mismatch: {mod['receipt']}")
for name,dep in M["direct_import_source_map"].items():
    q=ROOT/dep["repository_path"]
    if not q.is_file() or sha(q)!=dep["source_sha256"]: errors.append(f"direct source mismatch: {name} {dep['repository_path']}")
    if dep.get("producer_receipt_path"):
        r=ROOT/dep["producer_receipt_path"]
        if not r.is_file() or sha(r)!=dep["producer_receipt_sha256"]: errors.append(f"producer receipt mismatch: {name}")
if errors:
    print("FAIL\n"+"\n".join(errors)); raise SystemExit(1)
print("PASS: packet sources, receipts, direct imported source pins, and evidence hashes match")
