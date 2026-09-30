#!/usr/bin/env python3
"""Audit the R124 observed-prefix and ideal distinct-retry boundary."""
import hashlib
import json
from pathlib import Path

root = Path(__file__).parents[1]
evidence = root / "evidence/r124-observed-retry-law"
manifest = json.loads((Path(__file__).with_name("r124-release-manifest.json")).read_text())
receipt = json.loads((evidence / "receipt.json").read_text())
metadata = json.loads((evidence / "metadata.json").read_text())
failed = json.loads((evidence / "failed-formulations.json").read_text())
command = json.loads((evidence / "command.json").read_text())
pins = json.loads((evidence / "dependency-pins.json").read_text())

assert receipt["status"] == "PASS"
assert receipt["base_revision"] == manifest["base_revision"]
assert receipt["compiled"] == 4 and receipt["axiom_audits"] == 9
assert receipt["dependency_pins"] == len(pins) == 594
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
    assert "Quot.sound" in target["axioms"]

assert failed["status"] == "REPLACED"
assert all(x["swap"] == 0 for x in failed["attempts"])
claims = receipt["claims"]
assert claims["arbitrary_visible_q22_prefix"] is True
assert claims["conditional_q22_independent_answer_law"] is True
assert claims["guarded_cache_hit_is_visible_failure"] is True
assert claims["ideal_distinct_retry_failure_probability"] == "1 / sourceMinimum^3"
assert claims["inner_ood_sampler_law"] == "OPEN"
assert claims["actual_callback_prefix_freshness_or_loss"] == "OPEN"
assert claims["production_v6_distinct_wrapper"] is False
assert claims["full_privacy"] is False and claims["full_soundness"] is False

print(json.dumps({
    "status": "PASS",
    "compiled": receipt["compiled"],
    "axiom_audits": receipt["axiom_audits"],
    "first_remaining": receipt["first_remaining"],
}))
