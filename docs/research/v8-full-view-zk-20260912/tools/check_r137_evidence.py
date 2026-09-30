#!/usr/bin/env python3
"""Audit the R137 exact transcript extraction and R136 external closure."""
import hashlib
import json
from pathlib import Path

root = Path(__file__).parents[1]
ev = root / "evidence/r137-transcript-external-closure"
manifest = json.loads((ev / "manifest.json").read_text())
receipt = json.loads((ev / "receipt.json").read_text())
command = json.loads((ev / "command.json").read_text())

def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()

assert manifest["status"] == receipt["status"] == "PASS"
assert manifest["base_revision"] == receipt["base_revision"]
for target in manifest["targets"]:
    source = root / "lean" / (target["target"] + ".lean")
    log = ev / target["log"]
    assert digest(source) == target["sha256"], target["target"]
    text = log.read_text()
    assert "Exit status: 0" in text and "Swaps: 0" in text, target["log"]
for rel, expected in manifest["artifacts"].items():
    assert digest(ev / rel) == expected, rel

raw_funs = (ev / "generated/AspisR137Transcript/Funs.lean").read_text()
raw_types = (ev / "generated/AspisR137Transcript/Types.lean").read_text()
assert "structure transcript.Transcript" in raw_types
for name in ["new", "absorb", "challenge_qm31", "challenge_nonzero_qm31"]:
    assert f"def transcript.Transcript.{name}" in raw_funs
for name in ["PROFILE", "STATEMENT", "ROOT", "SECOND_PHASE_ROOT", "V6_POINT_CLAIMS"]:
    assert f"def transcript.label.{name}" in raw_funs
assert "axiom " not in raw_types and "axiom " not in raw_funs

external = (root / "lean/AspisR136BeforeOod/FunsExternal.lean").read_text()
for name in ["new", "absorb", "challenge_qm31", "challenge_nonzero_qm31"]:
    assert f"def aspis_core.transcript.Transcript.{name}" in external
assert "axiom " not in external
external_log = (ev / "logs/AspisR136BeforeOod_FunsExternal.log").read_text()
assert "to_from_qm31' does not depend on any axioms" in external_log
assert "from_to_qm31' does not depend on any axioms" in external_log

assert "MemorySwapMax=0" in " ".join(command["resource_scope"])
assert receipt["extraction"]["exit"] == receipt["translation"]["exit"] == 0
assert receipt["extraction"]["swap"] == receipt["translation"]["swap"] == 0
assert all(x["exit"] == 0 and x["swap"] == 0 for x in receipt["lean"])
assert receipt["generated"] == {
    "external_type_axioms": 0,
    "external_function_axioms": 0,
    "exact_labels": 5,
    "exact_operational_functions": 5,
}
assert receipt["claims"]["transcript_external_closure"] == "COMPILED"
assert receipt["claims"]["source_execution_bridge"] == "OPEN"
assert receipt["claims"]["actual_sampler_admissibility"] == "OPEN"
assert not receipt["claims"]["privacy"] and not receipt["claims"]["soundness"]
print(json.dumps({"status":"PASS","exact_transcript":"EXTRACTED",
                  "external_layer":"COMPILED","source_bridge":"OPEN",
                  "privacy":False,"soundness":False}))
