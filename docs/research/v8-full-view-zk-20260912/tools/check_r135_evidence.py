#!/usr/bin/env python3
"""Audit the verified R135 selected-schedule execution packet."""
import hashlib, json
from pathlib import Path

root = Path(__file__).parents[1]
ev = root / "evidence/r135-selected-schedule-execution"
manifest = json.loads((root / "tools/r135-release-manifest.json").read_text())
metadata = json.loads((ev / "metadata.json").read_text())
receipt = json.loads((ev / "receipt.json").read_text())
command = json.loads((ev / "command.json").read_text())
assert manifest["status"] == receipt["status"] == "PASS"
assert manifest["base_revision"] == receipt["base_revision"]
assert manifest["selected_callback_sha256"] == receipt["selected_callback_sha256"]
assert manifest["selected_callback_sha256"] == (
    "4f8f80e0847ec004a56fc693f6096308090de5f3cbed35722dba330afaa9820f")
assert metadata == [{k: x[k] for k in ("target", "sha256", "status")}
                    for x in manifest["targets"]]
assert receipt["compiled"] == 1 and receipt["pending"] == 0
assert receipt["memory_swap_max"] == 0
assert receipt["claims"]["rust_source_execution_bridge"] == "OPEN"
assert receipt["claims"]["source_sampler_distribution"] == "OPEN"
assert not receipt["claims"]["privacy"] and not receipt["claims"]["soundness"]
assert "MemorySwapMax=0" in " ".join(command["runner"])
assert "-M4500" in " ".join(command["command"])
target = manifest["targets"][0]
path = root / "lean" / (target["target"] + ".lean")
assert hashlib.sha256(path.read_bytes()).hexdigest() == target["sha256"]
log = (ev / "SelectedResearchScheduleExecution.log").read_text()
assert "exit 0" in log and "swap 0" in log
print(json.dumps({"status":"PASS","compiled":1,"pending":0,
                  "rust_source_execution_bridge":"OPEN"}))
