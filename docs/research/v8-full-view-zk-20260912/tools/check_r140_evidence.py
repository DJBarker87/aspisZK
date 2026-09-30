#!/usr/bin/env python3
"""Audit the R140 exact nonzero source/model evidence."""
import hashlib
import json
from pathlib import Path

root = Path(__file__).parents[1]
ev = root / "evidence/r140-nonzero-source-model"
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
for theorem in ["encodeWord_eq_zero_iff", "encodeQM31_eq_zero_iff",
                "generated_ne_zero_false", "generated_ne_zero_true",
                "bounded_model_exact", "nonzero_source_model_exact"]:
    assert f"R139NonzeroModelBridge.{theorem}' depends on axioms" in log

claims = manifest["claims"]
for name in ["encoded_zero_test", "finite_nonzero_model",
             "source_nonzero_model"]:
    assert claims[name] == "COMPILED"
for name in ["callback_execution", "q22_source_bridge"]:
    assert claims[name] == "OPEN"
assert not claims["privacy"] and not claims["soundness"]

print(json.dumps({"status": "PASS", "nonzero_source_model": "COMPILED",
                  "callback": "OPEN", "q22_source": "OPEN",
                  "privacy": False, "soundness": False}))
