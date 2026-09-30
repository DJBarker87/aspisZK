#!/usr/bin/env python3
"""Audit the verified R133 causal-prefix evidence packet."""
import hashlib, json
from pathlib import Path
root=Path(__file__).parents[1]; ev=root/"evidence/r133-causal-prefix-boundary"
m=json.loads((root/"tools/r133-release-manifest.json").read_text()); md=json.loads((ev/"metadata.json").read_text()); r=json.loads((ev/"receipt.json").read_text()); c=json.loads((ev/"command.json").read_text())
assert m["status"]==r["status"]=="PASS" and m["base_revision"]==r["base_revision"]
assert md==[{k:x[k] for k in ("target","sha256","status")} for x in m["targets"]]
assert r["compiled"]==9 and r["pending"]==0 and r["memory_swap_max"]==0
assert r["claims"]["bridge_premise"]=="OPEN" and r["claims"]["grind_source_callback_equivalence"]=="OPEN"
assert r["claims"]["source_sampler_distribution"]=="OPEN" and not r["claims"]["privacy"] and not r["claims"]["soundness"]
assert "MemorySwapMax=0" in " ".join(c["runner"]) and "-M4500" in " ".join(c["command"])
for x in m["targets"]:
 p=root/"lean"/(x["target"]+".lean"); assert p.exists() and hashlib.sha256(p.read_bytes()).hexdigest()==x["sha256"]
 log=(ev/(x["target"].split("/")[-1]+".log")).read_text(); assert "exit 0" in log and "swap 0" in log
print(json.dumps({"status":"PASS","compiled":9,"pending":0}))
