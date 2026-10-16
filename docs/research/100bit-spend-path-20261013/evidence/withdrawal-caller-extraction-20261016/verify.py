#!/usr/bin/env python3
"""Verify retained extraction evidence; does not compile or prove refinement."""
from pathlib import Path
import hashlib
import json
import tarfile

p = Path(__file__).resolve().parent
summary = json.loads((p / "SUMMARY.json").read_text())
raw = (p / "caller-extraction-evidence.tar.gz").read_bytes()
assert hashlib.sha256(raw).hexdigest() == summary["archive_sha256"]
with tarfile.open(p / "caller-extraction-evidence.tar.gz", "r:gz") as archive:
    for item in json.loads((p / "archive-members.json").read_text()):
        data = archive.extractfile(item["path"]).read()
        assert len(data) == item["bytes"]
        assert hashlib.sha256(data).hexdigest() == item["sha256"]
    for name, digest in summary["generated_files"].items():
        data = archive.extractfile("extraction-a/generated/" + name).read()
        assert hashlib.sha256(data).hexdigest() == digest
        assert data == (p.parents[1] / "lean/extracted-withdrawal-caller-20261016" / name).read_bytes()
    translation = json.loads(archive.extractfile("extraction-a/generated/translation.json").read())
    assert len(translation["functions"]) == 10
    assert not any(entry.get("is_opaque") for entry in translation["functions"])
    assert not translation["trait_decls"] and not translation["trait_impls"]
    for label in ["charon-a", "aeneas-a"]:
        receipt = json.loads(archive.extractfile("runs/" + label + "/receipt.json").read())
        assert receipt == summary["runs"][label]
        assert receipt["exit_status"] == receipt["swaps"] == 0
        assert receipt["limits"] == {"memory.high": "6442450944", "memory.max": "8589934592", "memory.swap.max": "0"}
print("PASS:21 member hashes, exact generated mirrors, two capped extraction receipts; Lean/refinement OPEN")
