#!/usr/bin/env python3
import hashlib, json, sys
from pathlib import Path

root = Path(__file__).resolve().parent
m = json.loads((root / "manifest.json").read_text())
assert m.get("schema") == "focused-extractor-proof-packet-v1"
assert m.get("packet") == root.name
assert m.get("lean_exit_status") == 0
assert m.get("compiled_objects_included") is False
assert m.get("object_in_packet") is False
assert m.get("closure_summary", {}).get("missing_modules") == []
assert m.get("closure_summary", {}).get("full_closure_file_retained") is False
assert m.get("axioms") == "Both exported theorem reports in evidence/lean.log: propext, Classical.choice, Quot.sound."
for entry in m["files"]:
    p = root / entry["path"]
    assert p.is_file(), entry["path"]
    b = p.read_bytes()
    assert len(b) == entry["bytes"], entry["path"]
    assert hashlib.sha256(b).hexdigest() == entry["sha256"], entry["path"]
    assert p.suffix not in {".olean", ".ilean", ".pyc", ".so", ".dylib"}, entry["path"]
for mod, pin in m["direct_imports"].items():
    assert len(pin["object_sha256"]) == 64, mod
print("PASS", m["packet"], "files", len(m["files"]))
