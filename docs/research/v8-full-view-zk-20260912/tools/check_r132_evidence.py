#!/usr/bin/env python3
"""Audit the verified R132 fixed-tape evidence packet."""
import hashlib, json
from pathlib import Path

root = Path(__file__).parents[1]
ev = root / "evidence/r132-uniform-fixed-tape-boundary"
m = json.loads((root / "tools/r132-release-manifest.json").read_text())
md = json.loads((ev / "metadata.json").read_text())
r = json.loads((ev / "receipt.json").read_text())
c = json.loads((ev / "command.json").read_text())
assert m["status"] == r["status"] == "PASS"
assert m["base_revision"] == r["base_revision"]
assert md == [{k: x[k] for k in ("target", "sha256", "status")} for x in m["targets"]]
assert r["compiled"] == 3 and r["pending"] == 0
assert r["claims"]["FreshFrom"] == "OPEN"
assert r["claims"]["source_callback_distribution"] == "OPEN"
assert r["claims"]["privacy"] is False and r["claims"]["soundness"] is False
for x in m["targets"]:
    p = root / "lean" / (x["target"] + ".lean")
    if x["status"] == "PASS":
        assert p.exists()
        assert hashlib.sha256(p.read_bytes()).hexdigest() == x["sha256"]
    log = (ev / (x["target"].split("/")[-1] + ".log")).read_text()
    assert "exit 0" in log and "swap 0" in log
assert "MemorySwapMax=0" in " ".join(c["runner"]) and "-M4500" in " ".join(c["command"])
assert not c.get("pending_targets")
assert r["compiled"] == len(m["targets"])
print(json.dumps({"status":"PASS", "compiled":3, "pending":0}))
