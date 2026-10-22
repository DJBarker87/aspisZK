#!/usr/bin/env python3
from pathlib import Path
import hashlib,json
root=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((root/"manifest.json").read_text()); r=json.loads((root/"receipt/receipt.json").read_text())
s=root/"sources/S4TraceLiteralOutputJoinV1.lean"
assert sha(s)==m["source_sha256"]==r["source_sha256"]
assert r["exit_status"]==0 and r["process_swaps"]==0 and r["watchdog_abort"] is None
assert r["object_sha256"]==m["object_sha256"]
assert m["axioms"]==["propext","Quot.sound"]
assert not list(root.rglob("*.olean")) and not list(root.rglob("*.llbc"))
print("PASS")
