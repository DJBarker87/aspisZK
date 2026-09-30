#!/usr/bin/env python3
"""Audit the R142 callback transcript-primitives evidence."""
import hashlib
import json
from pathlib import Path

root = Path(__file__).parents[1]
ev = root / "evidence/r142-before-ood-primitives"
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
for theorem in ["new_exact", "absorb_exact"]:
    assert f"R141BeforeOodPrimitiveBridge.{theorem}'" in log

claims = manifest["claims"]
for name in ["callback_transcript_new", "callback_packed_absorb",
             "callback_long_absorb"]:
    assert claims[name] == "COMPILED"
for name in ["before_ood_serializer", "before_ood_execution",
             "q22_source_bridge"]:
    assert claims[name] == "OPEN"
assert not claims["privacy"] and not claims["soundness"]

print(json.dumps({"status": "PASS", "new_absorb": "COMPILED",
                  "serializer": "OPEN", "before_ood": "OPEN",
                  "q22_source": "OPEN", "privacy": False,
                  "soundness": False}))
