#!/usr/bin/env python3
"""Audit the focused R131 cursor-boundary evidence."""
import hashlib, json
from pathlib import Path
root=Path(__file__).parents[1]
ev=root/"evidence/r131-cursor-tight-boundary"
m=json.loads((root/"tools/r131-release-manifest.json").read_text())
r=json.loads((ev/"receipt.json").read_text())
md=json.loads((ev/"metadata.json").read_text())
c=json.loads((ev/"command.json").read_text())
pins=json.loads((root/"evidence/r122-adaptive-first-read/dependency-pins.json").read_text())
assert m["base_revision"]==r["base_revision"]=="61b446d5b0f7adc30d313b375aee2b2e48040216"
assert len(pins)==r["dependency_pins"]==272 and md==m["targets"]
assert "MemorySwapMax=0" in " ".join(c["runner"]) and "-M4500" in c["command"]
for x in m["targets"]:
    p=root/"lean"/(x["target"]+".lean")
    assert hashlib.sha256(p.read_bytes()).hexdigest()==x["sha256"]
    log=(ev/(x["target"].split("/")[-1]+".log")).read_text()
    assert "exit 0" in log and "swaps 0" in log
assert r["compiled"]==2 and r["pending"]==0 and r["status"]=="PASS"
assert r["claims"]["FreshFrom"]=="OPEN" and r["claims"]["source_callback_distribution"]=="OPEN"
assert r["claims"]["privacy"] is False and r["claims"]["soundness"] is False
print(json.dumps({"status":"PASS","compiled":2,"pending":0}))
