#!/usr/bin/env python3
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
manifest = json.loads((ROOT / "manifest.json").read_text())
assert manifest["schema"] == "focused-extractor-proof-packet-v1"
assert manifest["packet"] == ROOT.name
for item in manifest["files"]:
    path = ROOT / item["path"]
    data = path.read_bytes()
    assert len(data) == item["size_bytes"], item["path"]
    assert hashlib.sha256(data).hexdigest() == item["sha256"], item["path"]
receipt = json.loads((ROOT / "receipts/receipt.json").read_text())
mod = manifest["modules"][0]
assert receipt["exit_status"] == mod["exit_status"] == 0
assert receipt["source_sha256"] == mod["source_sha256"]
assert receipt["object_sha256"] == mod["object_sha256"]
assert receipt["git_head_at_launch"] == mod["source_revision"]
assert receipt["argv"][1:3] == ["-j1", "-M4400"]
assert receipt["compiler_sha256"] == manifest["compiler"]["sha256"]
assert "depends on axioms: [propext, Classical.choice, Quot.sound]" in (
    ROOT / "receipts/audit-lean.log"
).read_text()
assert not any(p.suffix in {".olean", ".ilean", ".c", ".so", ".dylib"} for p in ROOT.rglob("*"))
print("packet checks passed")
