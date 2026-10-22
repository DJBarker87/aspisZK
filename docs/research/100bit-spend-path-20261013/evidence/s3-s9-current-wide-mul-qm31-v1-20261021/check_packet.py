#!/usr/bin/env python3
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
MANIFEST = ROOT / "manifest.json"

def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()

m = json.loads(MANIFEST.read_text())
assert m["schema"] == "focused-extractor-proof-packet-v1"
for mod in m["modules"]:
    for key in ("source", "receipt", "preflight", "command"):
        p = ROOT / mod[key]
        assert p.is_file(), f"missing {key}: {p}"
    assert sha(ROOT / mod["source"]) == mod["source_sha256"]
    receipt = json.loads((ROOT / mod["receipt"]).read_text())
    assert receipt["exit_status"] == mod["exit_status"] == 0
    assert receipt["source_sha256"] == mod["source_sha256"]
    assert receipt["object_sha256"] == mod["object_sha256"]
    assert abs(receipt["wall_seconds"] - mod["wall_seconds"]) < 0.001
for owner in m["direct_import_source_map"].values():
    p = Path(owner["repository_path"])
    if not p.is_absolute():
        p = ROOT.parents[4] / p
    assert p.is_file(), f"missing imported source {p}"
    assert sha(p) == owner["source_sha256"], f"source hash mismatch {p}"
    producer = Path(owner["producer_manifest"])
    if not producer.is_absolute():
        producer = ROOT.parents[4] / producer
    pm = json.loads(producer.read_text())
    found = any(
        item.get("object_sha256") == owner["object_sha256"] and
        item.get("source_sha256") == owner["source_sha256"]
        for item in pm.get("modules", [])
    )
    if not found:
        found = any(
            x.get("object_sha256") == owner["object_sha256"] and
            x.get("source_sha256") == owner["source_sha256"]
            for x in pm.get("direct_import_source_map", {}).values()
        )
    assert found, f"producer manifest does not pin owner: {producer}"
rust = ROOT.parents[4] / m["rust_source"]["path"]
assert rust.is_file() and sha(rust) == m["rust_source"]["sha256"]
for item in m["files"]:
    p = ROOT / item["path"]
    assert p.is_file(), f"missing packet file {p}"
    assert sha(p) == item["sha256"], f"file hash mismatch {p}"
    assert p.stat().st_size == item["size_bytes"], f"file size mismatch {p}"
print("PASS: packet source, receipt, and direct-import pins validate")
