#!/usr/bin/env python3
"""Audit the R139 exact sampler source evidence."""
import hashlib
import json
from pathlib import Path

root = Path(__file__).parents[1]
ev = root / "evidence/r139-exact-sampler-source"
manifest = json.loads((ev / "manifest.json").read_text())


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


assert manifest["status"] == "PASS"
for relative, expected in manifest["sources"].items():
    source = root / "lean" / relative
    assert digest(source) == expected, relative
    text = source.read_text()
    assert "sorry" not in text and "admit" not in text

for result in manifest["focused_compiles"]:
    assert result["exit"] == 0
    assert result["swap"] == 0
    assert result["peak_rss_kib"] < 8 * 1024 * 1024

log = (ev / "logs/R139SamplerSourceBridge.log").read_text()
assert "Exit status: 0" in log
assert "Swaps: 0" in log
assert "sorryAx" not in log
for theorem in ["qm31_source_exact", "nonzero_source_unfolds"]:
    assert f"R139SamplerSourceBridge.{theorem}' depends on axioms" in log

claims = manifest["claims"]
for name in ["bounded_wrapping_reader", "qm31_source_execution",
             "nonzero_source_unfolding"]:
    assert claims[name] == "COMPILED"
for name in ["nonzero_model_correspondence", "callback_execution"]:
    assert claims[name] == "OPEN"
assert not claims["privacy"] and not claims["soundness"]

print(json.dumps({"status": "PASS", "qm31_source": "COMPILED",
                  "nonzero_unfolding": "COMPILED",
                  "nonzero_model": "OPEN", "callback": "OPEN",
                  "privacy": False, "soundness": False}))
