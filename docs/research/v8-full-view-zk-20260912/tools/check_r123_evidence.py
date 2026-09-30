#!/usr/bin/env python3
"""Audit the R123 source-domain and one-step first-read boundary."""
import hashlib
import json
from pathlib import Path

root = Path(__file__).parents[1]
evidence = root / "evidence/r123-source-domain-bound"
manifest = json.loads((Path(__file__).with_name("r123-release-manifest.json")).read_text())
receipt = json.loads((evidence / "receipt.json").read_text())
metadata = json.loads((evidence / "metadata.json").read_text())
failed = json.loads((evidence / "failed-formulations.json").read_text())
command = json.loads((evidence / "command.json").read_text())

assert receipt["status"] == "PASS"
assert receipt["base_revision"] == manifest["base_revision"]
assert receipt["compiled"] == 6 and receipt["axiom_audits"] == 17
assert receipt["dependency_pins"] == len(json.loads((evidence / "dependency-pins.json").read_text())) == 272
assert metadata == manifest["targets"]
assert command["targets"] == [x["target"] for x in manifest["targets"]]
assert "MemorySwapMax=0" in command["runner"] and "-M4500" in command["command"]

for item in manifest["targets"]:
    path = root / "lean" / (item["target"] + ".lean")
    assert hashlib.sha256(path.read_bytes()).hexdigest() == item["sha256"]
    log = (evidence / (item["target"].split("/")[-1] + ".log")).read_text()
    assert "Exit status: 0" in log and "Swaps: 0" in log
    assert "sorryAx" not in log
    assert "depends on axioms" in log

for target in receipt["targets"]:
    assert target["exit"] == 0 and target["swap"] == 0
    assert target["peak_rss_kib"] < 7 * 1024 * 1024
    assert "propext" in target["axioms"] and "Quot.sound" in target["axioms"]

assert failed["status"] == "REPLACED"
assert all(x["peak_rss_kib"] > 4_500_000 and x["swap"] == 0 for x in failed["failed_attempts"])
assert failed["replacement"]["exit"] == 0
claims = receipt["claims"]
assert claims["one_squeeze_source_bridge"] is True
assert claims["secure_ood_domain_cardinality"] == "P^2 * (P^2 - 1)"
assert claims["distinct_ood_acceptance_ratio"] == "EXPLICIT_NOT_SIMPLIFIED"
assert claims["actual_source_sampler_law"] == "OPEN"
assert claims["full_privacy"] is False and claims["full_soundness"] is False

print(json.dumps({
    "status": "PASS",
    "compiled": receipt["compiled"],
    "axiom_audits": receipt["axiom_audits"],
    "first_remaining": receipt["first_remaining"],
}))
