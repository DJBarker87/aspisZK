#!/usr/bin/env python3
import hashlib, json
from pathlib import Path
P = Path(__file__).resolve().parent
m = json.loads((P / "manifest.json").read_text())
assert m["schema"] == "focused-extractor-proof-packet-v1"
for rel, expected in m["files"].items():
    p = P / rel
    assert p.is_file(), f"missing {rel}"
    got = hashlib.sha256(p.read_bytes()).hexdigest()
    assert got == expected, f"hash mismatch {rel}: {got} != {expected}"
for mod in m["modules"]:
    source = P / mod["source"]
    assert hashlib.sha256(source.read_bytes()).hexdigest() == mod["source_sha256"]
for name, pin in m["direct_import_source_map"].items():
    source = P / pin["source_path"]
    assert hashlib.sha256(source.read_bytes()).hexdigest() == pin["source_sha256"]
print("source-only packet checks passed")
