#!/usr/bin/env python3
from pathlib import Path
import hashlib
import json

PACKET = Path(__file__).resolve().parent
MANIFEST = json.loads((PACKET / "manifest.json").read_text())
sha = lambda b: hashlib.sha256(b).hexdigest()
repo = next(p for p in PACKET.parents if (p / ".git").exists())
assert MANIFEST["schema"] == "focused-extractor-proof-packet-v1"
for rel, expected in MANIFEST["evidence_files"].items():
    assert sha((PACKET / rel).read_bytes()) == expected, rel
for module in MANIFEST["modules"]:
    source = PACKET / module["source"]
    receipt_path = PACKET / module["receipt"]
    receipt = json.loads(receipt_path.read_text())
    assert sha(source.read_bytes()) == module["source_sha256"]
    assert sha(receipt_path.read_bytes()) == module["receipt_sha256"]
    assert receipt["source_sha256"] == module["source_sha256"]
    assert receipt["object_sha256"] == module["object_sha256"]
    assert receipt["exit_status"] == module["exit_status"] == 0
    assert module["axioms"] == ["propext", "Classical.choice", "Quot.sound"]
for owner in MANIFEST["direct_import_source_map"].values():
    path = repo / owner["repository_path"]
    assert sha(path.read_bytes()) == owner["source_sha256"]
assert not list(PACKET.rglob("*.olean"))
print("PASS: source, receipt, direct imports, and no-binary policy")
