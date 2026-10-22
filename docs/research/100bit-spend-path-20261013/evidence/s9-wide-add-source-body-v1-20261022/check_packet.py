#!/usr/bin/env python3
import hashlib
import json
from pathlib import Path

base = Path(__file__).resolve().parent
manifest = json.loads((base / "manifest.json").read_text())
assert manifest["schema"] == "focused-source-extraction-packet-v1"
assert manifest["compiled_objects_included"] is False
assert manifest["llbc_included"] is False
for rel, expected in manifest["files"].items():
    path = base / rel
    assert path.is_file(), f"missing file: {rel}"
    got = hashlib.sha256(path.read_bytes()).hexdigest()
    assert got == expected, f"hash mismatch: {rel}: {got} != {expected}"
for path in base.rglob("*"):
    if path.is_file():
        assert path.suffix not in {".olean", ".ilean", ".pyc", ".llbc"}, f"forbidden artifact: {path}"
ids = json.loads((base / "attempt5/metadata/source-identities.json").read_text())
assert ids["actual_core_field"]["sha256"] == "28df5a1abee13bde4b3aa9eeceb0489bedf00531f298460954a97661f5f1baea"
assert ids["actual_core_wide_exact"]["sha256"] == "6260fa9d179328714e7df59640abb7a76a326e98900993ce7d3da98c6411d10b"
assert ids["opaque_arithmetic_bodies"]["WideExact.add"]["method_body_sha256"] == manifest["claim_boundary"]["target_body_sha256"]
receipt = json.loads((base / "attempt5/metadata/aeneas-receipt.json").read_text())
assert receipt["exit_status"] == 0 and not receipt["timed_out"]
assert receipt["limits"]["memory.high"] == "2147483648"
assert receipt["limits"]["memory.max"] == "4294967296"
assert receipt["limits"]["memory.swap.max"] == "0"
print("PASS: source extraction provenance, hashes, and artifact exclusions")
