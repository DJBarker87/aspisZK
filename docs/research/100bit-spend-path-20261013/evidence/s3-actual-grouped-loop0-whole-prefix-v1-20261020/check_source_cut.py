#!/usr/bin/env python3
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
MANIFEST = json.loads((ROOT / "manifest.json").read_text())
assert MANIFEST["schema"] == "focused-extractor-proof-packet-v1"
assert MANIFEST["source_cut_checker"] == "check_source_cut.py"
for rel, expected in MANIFEST["files"].items():
    p = ROOT / rel
    assert p.is_file(), f"missing packet file: {rel}"
    got = hashlib.sha256(p.read_bytes()).hexdigest()
    assert got == expected, f"hash mismatch: {rel}: {got} != {expected}"
for p in ROOT.rglob("*"):
    if p.is_file():
        assert p.suffix not in {".olean", ".ir", ".exe", ".tar", ".gz"}, f"binary artifact retained: {p}"
assert len(MANIFEST["modules"]) == 1
m = MANIFEST["modules"][0]
source = ROOT / m["source"]
assert hashlib.sha256(source.read_bytes()).hexdigest() == m["source_sha256"]
receipt_path = ROOT / m["receipt"]
assert hashlib.sha256(receipt_path.read_bytes()).hexdigest() == m["receipt_sha256"]
receipt = json.loads(receipt_path.read_text())
assert receipt["exit_status"] == 0 and receipt["object_sha256"] == m["object_sha256"]
assert receipt["source_sha256"] == m["source_sha256"]
assert receipt["scope_swap_peak_bytes"] == 0
assert m["swap_peak_bytes"] == 0
assert m["resource_caps"] == {
    "memory.high": "1073741824",
    "memory.max": "2147483648",
    "memory.swap.max": "0",
}
for theorem in (
    "actual_loop0_body_prefix_step",
    "actual_loop0_whole_prefix",
):
    assert theorem in (ROOT / m["lean_log"]).read_text()
assert "sorryAx" not in (ROOT / m["lean_log"]).read_text()
assert sorted(m["axioms"]) == ["Classical.choice", "Quot.sound", "propext"]
assert MANIFEST["direct_import_source_map"] == m["direct_imports"]
for mod, ref in m["direct_imports"].items():
    assert hashlib.sha256((ROOT / ref["source_path"]).read_bytes()).hexdigest() == ref["source_sha256"], mod
print("PASS: source-only whole-prefix packet, direct import sources, selected pins, receipt, and standard axioms")
