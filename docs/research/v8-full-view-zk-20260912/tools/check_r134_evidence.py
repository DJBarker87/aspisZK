#!/usr/bin/env python3
"""Audit the verified R134 selected-schedule evidence packet."""
import hashlib, json
from pathlib import Path

root = Path(__file__).parents[1]
ev = root / "evidence/r134-selected-schedule-bound"
manifest = json.loads((root / "tools/r134-release-manifest.json").read_text())
metadata = json.loads((ev / "metadata.json").read_text())
receipt = json.loads((ev / "receipt.json").read_text())
command = json.loads((ev / "command.json").read_text())

assert manifest["status"] == receipt["status"] == "PASS"
assert manifest["base_revision"] == receipt["base_revision"]
assert metadata == [{k: x[k] for k in ("target", "sha256", "status")}
                    for x in manifest["targets"]]
assert receipt["compiled"] == 2 and receipt["pending"] == 0
assert receipt["memory_swap_max"] == 0
assert receipt["claims"]["exact_read_bound"] == 1815
assert receipt["claims"]["rust_source_execution_bridge"] == "OPEN"
assert receipt["claims"]["source_sampler_distribution"] == "OPEN"
assert not receipt["claims"]["privacy"] and not receipt["claims"]["soundness"]
assert "MemorySwapMax=0" in " ".join(command["runner"])
assert "-M4500" in " ".join(command["command"])
for target in manifest["targets"]:
    path = root / "lean" / (target["target"] + ".lean")
    assert path.exists()
    assert hashlib.sha256(path.read_bytes()).hexdigest() == target["sha256"]
    log = (ev / (target["target"].split("/")[-1] + ".log")).read_text()
    assert "exit 0" in log and "swap 0" in log
print(json.dumps({"status": "PASS", "compiled": 2, "pending": 0,
                  "exact_read_bound": 1815}))
