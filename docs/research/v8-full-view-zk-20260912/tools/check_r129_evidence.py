#!/usr/bin/env python3
"""Audit the R129 answer-transport/history boundary."""
import hashlib, json
from pathlib import Path
root = Path(__file__).parents[1]
ev = root / "evidence/r129-answer-history-boundary"
manifest = json.loads((root / "tools/r129-release-manifest.json").read_text())
receipt = json.loads((ev / "receipt.json").read_text())
metadata = json.loads((ev / "metadata.json").read_text())
command = json.loads((ev / "command.json").read_text())
pins = json.loads((root / "evidence/r122-adaptive-first-read/dependency-pins.json").read_text())
assert manifest["base_revision"] == receipt["base_revision"] == "4ad6c579f47a4433b9c291b2efd4eac028dbf84b"
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
assert receipt["compiled"] == 2 and receipt["axiom_audits"] == 6
assert all(x["exit"] == 0 and x["swap"] == 0 for x in receipt["targets"])
claims = receipt["claims"]
assert claims["freshFrom_conditional_independentMean"] == "EXPLICIT_PREMISE"
assert claims["prefix_freshFrom_or_collision_loss"] == "OPEN"
assert claims["flat_raw_answers_with_advance_ghosts"] == "OPEN"
assert claims["rust_callback_equivalence"] == "OPEN"
assert claims["privacy"] is False and claims["soundness"] is False
print(json.dumps({"status":"PASS","compiled":2,"axiom_audits":6,"first_remaining":receipt["first_remaining"]}))
