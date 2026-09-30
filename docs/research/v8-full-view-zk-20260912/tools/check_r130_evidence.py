#!/usr/bin/env python3
"""Audit the partial R130 raw-independent boundary."""
import hashlib, json
from pathlib import Path
root=Path(__file__).parents[1]; ev=root/"evidence/r130-raw-independent-boundary"
m=json.loads((root/"tools/r130-release-manifest.json").read_text()); r=json.loads((ev/"receipt.json").read_text()); md=json.loads((ev/"metadata.json").read_text()); c=json.loads((ev/"command.json").read_text()); pins=json.loads((root/"evidence/r122-adaptive-first-read/dependency-pins.json").read_text())
assert m["base_revision"]==r["base_revision"]=="56d4a311483bb3bb88780e13e4b9e8969b8516b7"
assert len(pins)==r["dependency_pins"]==272 and md==m["targets"]
assert "MemorySwapMax=0" in " ".join(c["runner"]) and "-M4500" in c["command"]
for x in m["targets"]:
 p=root/"lean"/(x["target"]+".lean"); assert hashlib.sha256(p.read_bytes()).hexdigest()==x["sha256"]
 if x["status"]=="PASS":
  log=(ev/(x["target"].split("/")[-1]+".log")).read_text(); assert "exit 0" in log and "swaps 0" in log
assert r["compiled"]==3 and r["pending"]==0 and r["status"]=="PASS"
assert r["claims"]["FreshFrom"]=="OPEN" and r["claims"]["source_callback_distribution"]=="OPEN"
assert r["claims"]["privacy"] is False and r["claims"]["soundness"] is False
print(json.dumps({"status":"PASS","compiled":3,"pending":0}))
