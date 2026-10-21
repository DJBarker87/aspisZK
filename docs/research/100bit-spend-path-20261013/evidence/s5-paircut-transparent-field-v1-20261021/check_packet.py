#!/usr/bin/env python3
"""Verify the source-only transparent-reader extraction packet pins."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
manifest = json.loads((ROOT / "manifest.json").read_text())

for line in (ROOT / "SHA256SUMS").read_text().splitlines():
    expected, rel = line.split("  ", 1)
    actual = hashlib.sha256((ROOT / rel).read_bytes()).hexdigest()
    assert actual == expected, f"checksum mismatch: {rel}"

assert manifest["schema"] == "focused-extractor-proof-packet-v1"
assert manifest["llbc"]["has_errors"] is False
assert manifest["llbc"]["fun_decls"] > 0
assert manifest["llbc"]["type_decls"] > 0
for stage in ("charon", "aeneas"):
    assert manifest["extraction"][stage]["exit_status"] == 0
    assert manifest["extraction"][stage]["process_swaps"] == 0

for rel, expected in manifest["generated"]["files"].items():
    actual = hashlib.sha256(
        (ROOT / ("generated/AspisR1WeightsPairCut" if rel.endswith(".lean") else "generated") / rel).read_bytes()
    ).hexdigest()
    assert actual == expected, f"generated output mismatch: {rel}"

source_pins = json.loads((ROOT / "source/source-pins.json").read_text())
for name, expected in source_pins["kit_files"].items():
    actual = hashlib.sha256((ROOT / "source" / name).read_bytes()).hexdigest()
    assert actual == expected, f"source pin mismatch: {name}"

print("PASS: source, receipt, and generated-output pins agree")
