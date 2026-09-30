#!/usr/bin/env python3
"""Audit the R138 exact transcript primitive evidence."""
import hashlib
import json
from pathlib import Path

root = Path(__file__).parents[1]
ev = root / "evidence/r138-transcript-primitives"
manifest = json.loads((ev / "manifest.json").read_text())

def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()

assert manifest["status"] == "PASS"
lean = manifest["lean"]
source = root / "lean" / (lean["target"] + ".lean")
assert digest(source) == lean["sha256"]
lean_log = (ev / lean["log"]).read_text()
assert "Exit status: 0" in lean_log
assert "Swaps: 0" in lean_log
assert "sorryAx" not in lean_log
for theorem in [
    "new_execution", "profile_label", "statement_label", "root_label",
    "second_phase_root_label", "point_claims_label", "dom_absorb_byte",
    "packed_payload_limit", "squeeze_execution", "squeeze_source_step",
    "long_absorb_execution", "short_absorb_execution",
]:
    assert f"R137TranscriptPrimitiveBridge.{theorem}' depends on axioms" in lean_log

rust = manifest["rust"]
assert digest(ev / rust["test"]) == rust["sha256"]
rust_log = (ev / rust["log"]).read_text()
assert "4 passed; 0 failed" in rust_log

claims = manifest["claims"]
for name in ["initialization", "labels", "long_absorb_address",
             "packed_absorb_address", "squeeze_advance_addresses"]:
    assert claims[name] == "COMPILED"
for name in ["r137_sampler_bridge", "callback_execution"]:
    assert claims[name] == "OPEN"
assert not claims["privacy"] and not claims["soundness"]
print(json.dumps({"status": "PASS", "long_absorb": "COMPILED",
                  "squeeze": "COMPILED", "packed_absorb": "COMPILED",
                  "sampler": "OPEN", "privacy": False,
                  "soundness": False}))
