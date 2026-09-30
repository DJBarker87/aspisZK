#!/usr/bin/env python3
"""Audit the R125 circle-source/ideal-OOD boundary."""
import hashlib
import json
from pathlib import Path

root = Path(__file__).parents[1]
evidence = root / "evidence/r125-circle-source-boundary"
manifest = json.loads((Path(__file__).with_name("r125-release-manifest.json")).read_text())
receipt = json.loads((evidence / "receipt.json").read_text())
metadata = json.loads((evidence / "metadata.json").read_text())
failed = json.loads((evidence / "failed-formulations.json").read_text())
command = json.loads((evidence / "command.json").read_text())
pins = json.loads((evidence / "dependency-pins.json").read_text())

assert receipt["status"] == "PASS"
assert receipt["base_revision"] == manifest["base_revision"]
assert receipt["compiled"] == 2 and receipt["axiom_audits"] == 10
assert receipt["dependency_pins"] == len(pins) == 629
assert metadata == manifest["targets"]
assert command["targets"] == [x["target"] for x in manifest["targets"]]
assert "MemorySwapMax=0" in command["runner"] and "-M4500" in command["command"]

for item in manifest["targets"]:
    path = root / "lean" / (item["target"] + ".lean")
    assert hashlib.sha256(path.read_bytes()).hexdigest() == item["sha256"]
    log = (evidence / (item["target"].split("/")[-1] + ".log")).read_text()
    assert "Exit status: 0" in log and "Swaps: 0" in log
    assert "sorryAx" not in log and "depends on axioms" in log

for target in receipt["targets"]:
    assert target["exit"] == 0 and target["swap"] == 0
    assert target["peak_rss_kib"] < 7 * 1024 * 1024

assert failed["status"] == "REPLACED"
assert failed["attempts"][0]["swap"] == 0
claims = receipt["claims"]
assert claims["actual_circle_observer_arbitrary_history"] is True
assert claims["source_acceptance_predicate_is_im_nonzero"] is True
assert claims["ideal_ood_accepted_outputs_equiprobable"] is True
assert claims["byte_tape_to_uniform_qm31"] == "OPEN"
assert claims["callback_prefix_freshness_or_loss"] == "OPEN"
assert claims["full_privacy"] is False and claims["full_soundness"] is False

print(json.dumps({"status": "PASS", "compiled": 2,
  "axiom_audits": 10, "first_remaining": receipt["first_remaining"]}))
