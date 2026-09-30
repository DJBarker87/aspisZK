#!/usr/bin/env python3
"""Audit the R126 focused sampler-representation boundary."""
import hashlib, json
from pathlib import Path

root = Path(__file__).parents[1]
ev = root / "evidence/r126-sampler-prefix-boundary"
manifest = json.loads((root / "tools/r126-release-manifest.json").read_text())
receipt = json.loads((ev / "receipt.json").read_text())
metadata = json.loads((ev / "metadata.json").read_text())
command = json.loads((ev / "command.json").read_text())
failed = json.loads((ev / "failed-formulations.json").read_text())
pins = json.loads((root / "evidence/r122-adaptive-first-read/dependency-pins.json").read_text())

assert manifest["base_revision"] == receipt["base_revision"] == "3c06a11a80d253506aaadb00f810943f69eb525b"
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
assert failed["status"] == "OPEN"
assert receipt["claims"]["source_sampler_distribution"] == "OPEN"
assert receipt["claims"]["callback_oracle_equivalence"] == "OPEN"
assert receipt["claims"]["privacy"] is False and receipt["claims"]["soundness"] is False
print(json.dumps({"status":"PASS","compiled":2,"axiom_audits":4,"first_remaining":receipt["first_remaining"]}))
