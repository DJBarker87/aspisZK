#!/usr/bin/env python3
"""Validate the source-only S5 row-28 proof packet without Lean objects."""
from __future__ import annotations
import hashlib, json, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent
MANIFEST = ROOT / "manifest.json"

def sha(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for block in iter(lambda: f.read(1 << 20), b""):
            h.update(block)
    return h.hexdigest()

def fail(message: str) -> None:
    print(f"FAIL: {message}", file=sys.stderr)
    raise SystemExit(1)

m = json.loads(MANIFEST.read_text())
if m.get("schema") != "focused-extractor-proof-packet-v1":
    fail("unexpected schema")
listed = {entry["path"]: entry for entry in m.get("files", [])}
actual = {p.relative_to(ROOT).as_posix() for p in ROOT.rglob("*") if p.is_file() and p.name not in {"manifest.json", "SHA256SUMS"}}
if actual != set(listed):
    fail(f"manifest file coverage differs: unlisted={sorted(actual-set(listed))}, missing={sorted(set(listed)-actual)}")
for rel, entry in listed.items():
    path = ROOT / rel
    if sha(path) != entry.get("sha256") or path.stat().st_size != entry.get("size_bytes"):
        fail(f"file pin mismatch: {rel}")
    if path.suffix in {".olean", ".ilean", ".ir", ".llbc"}:
        fail(f"compiled/binary artifact present: {rel}")

for module in m.get("modules", []):
    src = ROOT / module["source"]
    if sha(src) != module["source_sha256"]:
        fail(f"module source mismatch: {module['module']}")
    receipt = json.loads((ROOT / module["receipt"]).read_text())
    command = json.loads((ROOT / module["command"]).read_text())
    if receipt.get("exit_status") != 0 or module.get("exit_status") != 0:
        fail(f"nonzero producer: {module['module']}")
    obj_hash = receipt.get("object_sha256")
    if obj_hash != module.get("object_sha256"):
        fail(f"object receipt mismatch: {module['module']}")
    if command.get("source_sha256") != module["source_sha256"]:
        fail(f"command source pin mismatch: {module['module']}")
    argv = command.get("argv", [])
    if "-j1" not in argv or "-M" not in argv or "4400" not in argv:
        fail(f"missing required focused Lean flags: {module['module']}")
    if receipt.get("swaps", receipt.get("swap_count", 0)) != 0:
        fail(f"swap was used: {module['module']}")
    log = (ROOT / module["log"]).read_text()
    if module.get("axiom_audit", "").startswith("Type-only"):
        if log.strip(): fail(f"unexpected log content for type-only owner: {module['module']}")
    else:
        if "depends on axioms:" not in log:
            fail(f"missing axiom audit: {module['module']}")
        for axiom in module.get("axioms", []):
            if axiom not in log: fail(f"axiom audit omits {axiom}: {module['module']}")
    if "sorryAx" in log:
        fail(f"sorryAx audit result: {module['module']}")

for name, owner in m.get("direct_import_source_map", {}).items():
    if "source" in owner:
        source = ROOT / owner["source"]
        if not source.is_file() or sha(source) != owner["source_sha256"]:
            fail(f"direct import source mismatch: {name}")
    producer = owner.get("producer_packet")
    if producer and not (ROOT.parents[1] / producer).is_file():
        fail(f"producer packet reference missing: {name}: {producer}")

checksums = ROOT / "SHA256SUMS"
if checksums.exists():
    for line in checksums.read_text().splitlines():
        expected, rel = line.split("  ", 1)
        path = ROOT / rel
        if not path.is_file() or sha(path) != expected:
            fail(f"SHA256SUMS mismatch: {rel}")
print(f"PASS: {len(listed)} source/evidence files, {len(m.get('modules', []))} module receipts, no binaries")
