#!/usr/bin/env python3
"""Audit the R141 selected-callback sampler evidence."""
import hashlib
import json
from pathlib import Path

root = Path(__file__).parents[1]
ev = root / "evidence/r141-before-ood-sample"
manifest = json.loads((ev / "manifest.json").read_text())


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


assert manifest["status"] == "PASS"
lean = manifest["lean"]
source = root / "lean" / (lean["target"] + ".lean")
assert digest(source) == lean["sha256"]
text = source.read_text()
assert "sorry" not in text and "admit" not in text

log = (ev / lean["log"]).read_text()
assert "Exit status: 0" in log
assert "Swaps: 0" in log
assert "sorryAx" not in log
for theorem in ["map_err_mapChallenge", "sample_false_exact",
                "sample_true_exact"]:
    name = f"R140BeforeOodSampleBridge.{theorem}'"
    assert name in log

claims = manifest["claims"]
for name in ["ordinary_sample_callback", "nonzero_sample_callback",
             "callback_error_mapping"]:
    assert claims[name] == "COMPILED"
for name in ["before_ood_serializer", "before_ood_execution",
             "q22_source_bridge"]:
    assert claims[name] == "OPEN"
assert not claims["privacy"] and not claims["soundness"]

print(json.dumps({"status": "PASS", "sample_callback": "COMPILED",
                  "serializer": "OPEN", "before_ood": "OPEN",
                  "q22_source": "OPEN", "privacy": False,
                  "soundness": False}))
