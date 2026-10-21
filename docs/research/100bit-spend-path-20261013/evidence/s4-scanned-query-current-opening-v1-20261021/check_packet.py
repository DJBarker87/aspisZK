#!/usr/bin/env python3
"""Verify the source-only S4 current-opening packet without Lean replay."""
from pathlib import Path
import hashlib
import json
import re
import sys

HERE = Path(__file__).resolve().parent
manifest = json.loads((HERE / "manifest.json").read_text())

def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()

listed = {row["path"]: row for row in manifest["payload_files"]}
actual = {
    str(path.relative_to(HERE))
    for path in HERE.rglob("*")
    if path.is_file() and path.name not in {"manifest.json", "SHA256SUMS", "check_packet.py", "README.md"}
}
assert actual == set(listed), (actual - set(listed), set(listed) - actual)
for rel, row in listed.items():
    path = HERE / rel
    assert sha(path) == row["sha256"], rel
    assert path.stat().st_size == row["size"], rel

# A source-only packet must not accidentally include compiled artifacts.
assert not [p for p in HERE.rglob("*") if p.is_file() and p.suffix in {".olean", ".ilean", ".o", ".a", ".so"}]

src = HERE / manifest["source_file"]
assert sha(src) == manifest["source_sha256"]
result = json.loads((HERE / "receipts/v13-result.json").read_text())
launch = json.loads((HERE / "receipts/v13-launch.json").read_text())
preflight = json.loads((HERE / "receipts/v13-preflight.json").read_text())
assert result["exit"] == 0
assert result["source_sha256_at_launch"] == manifest["source_sha256"]
assert result["source_sha256_at_end"] == manifest["source_sha256"]
assert result["object_sha256"] == manifest["object_sha256"]
assert launch["source_sha256"] == manifest["source_sha256"]
assert launch["git_revision"] == manifest["source_revision"]
assert preflight["launch_git_revision"] == manifest["source_revision"]
assert preflight["argv"][1:3] == ["-j1", "-M4400"]

lean_log = (HERE / "receipts/v13-lean.log").read_text()
assert "depends on axioms: [propext," in lean_log
assert "Classical.choice" in lean_log and "Quot.sound" in lean_log
assert "sorryAx" not in lean_log
time_log = (HERE / "receipts/v13-time.log").read_text()
assert re.search(r"\b0\s+swaps\b", time_log)

rust = (HERE / "rust/candidate.rs").read_text()
opening_span = (
    "fn opening(proof: &[u8], i: usize) -> &[u8] {\n"
    "    let at = compact::OFF_OPENINGS + i * OPENING;\n"
    "    &proof[at..at + OPENING]\n}"
)
assert opening_span in rust
assert hashlib.sha256(opening_span.encode()).hexdigest() == manifest["rust_source_pin"]["function_span_sha256"]
assert sha(HERE / "rust/candidate.rs") == manifest["rust_source_pin"]["sha256"]

print("S4 current-opening packet checks passed")
