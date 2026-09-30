#!/usr/bin/env python3
"""Audit the R127 cursor/distinct-circle boundary."""
import hashlib, json
from pathlib import Path

root = Path(__file__).parents[1]
ev = root / "evidence/r127-cursor-distinct-boundary"
manifest = json.loads((root / "tools/r127-release-manifest.json").read_text())
receipt = json.loads((ev / "receipt.json").read_text())
metadata = json.loads((ev / "metadata.json").read_text())
command = json.loads((ev / "command.json").read_text())
pins = json.loads((root / "evidence/r122-adaptive-first-read/dependency-pins.json").read_text())
assert manifest["base_revision"] == receipt["base_revision"] == "e5ad5468925e3a15b36a3347230b850e511f15d2"
assert len(pins) == receipt["dependency_pins"] == 272
assert metadata == manifest["targets"]
assert command["targets"] == [x["target"] for x in manifest["targets"]]
assert "MemorySwapMax=0" in " ".join(command["runner"]) and "-M4500" in command["command"]
for item in manifest["targets"]:
    path = root / "lean" / (item["target"] + ".lean")
    assert hashlib.sha256(path.read_bytes()).hexdigest() == item["sha256"]
    log = (ev / (item["target"].split("/")[-1] + ".log")).read_text()
    assert "Exit status: 0" in log and "Swaps: 0" in log
    assert "sorryAx" not in log and "depends on axioms" in log
assert receipt["compiled"] == 2 and receipt["axiom_audits"] == 4
assert all(x["exit"] == 0 and x["swap"] == 0 for x in receipt["targets"])
claims = receipt["claims"]
assert claims["limb_whole_challenge_raw_stream_composition"] == "OPEN"
assert claims["callback_equivalence_freshness_distribution"] == "OPEN"
assert claims["privacy"] is False and claims["soundness"] is False
print(json.dumps({"status":"PASS","compiled":2,"axiom_audits":4,"first_remaining":receipt["first_remaining"]}))
