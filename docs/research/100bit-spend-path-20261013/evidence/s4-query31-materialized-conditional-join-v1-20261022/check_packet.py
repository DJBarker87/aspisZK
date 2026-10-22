#!/usr/bin/env python3
"""Validate the source-only S4 row-31 materialized conditional-join packet."""
from __future__ import annotations
import hashlib
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parent
EXPECTED = {
    "S4SourcePairsToFunctionsV1": "sources/S4SourcePairsToFunctionsV1.lean",
    "S4Query31MaterializedConditionalJoinV1": "sources/S4Query31MaterializedConditionalJoinV1.lean",
}
AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()

def fail(message: str) -> None:
    raise SystemExit(message)

manifest = json.loads((ROOT / "manifest.json").read_text())
if manifest.get("source_only") is not True or manifest.get("objects_committed") is not False:
    fail("manifest must describe a source-only packet without compiled objects")
if set(manifest.get("targets", [])) != set(EXPECTED):
    fail("manifest target list differs from the two checked targets")

# Verify the complete packet checksum inventory (the inventory does not hash itself).
checksums = {}
for line in (ROOT / "SHA256SUMS").read_text().splitlines():
    digest, rel = line.split(None, 1)
    rel = rel.strip()
    if rel in checksums:
        fail(f"duplicate SHA256SUMS entry: {rel}")
    checksums[rel] = digest
actual_files = {str(p.relative_to(ROOT)) for p in ROOT.rglob("*") if p.is_file() and p.name != "SHA256SUMS"}
if actual_files != set(checksums):
    fail(f"SHA256SUMS file inventory mismatch: missing={sorted(actual_files-set(checksums))}, stale={sorted(set(checksums)-actual_files)}")
for rel, digest in checksums.items():
    if sha(ROOT / rel) != digest:
        fail(f"checksum mismatch: {rel}")

for target, source_rel in EXPECTED.items():
    receipt_path = ROOT / "receipt" / ("helper_receipt.json" if target == "S4SourcePairsToFunctionsV1" else "consumer_receipt.json")
    log_path = ROOT / "receipt" / ("helper_lean.log" if target == "S4SourcePairsToFunctionsV1" else "consumer_lean.log")
    receipt = json.loads(receipt_path.read_text())
    source = ROOT / source_rel
    if receipt.get("exit_status") != 0:
        fail(f"{target} did not exit successfully")
    if receipt.get("source_sha256") != sha(source):
        fail(f"{target} source hash does not match receipt")
    if receipt.get("process_swaps") != 0 or not isinstance(receipt.get("peak_process_rss_bytes"), int):
        fail(f"{target} receipt lacks a valid no-swap RSS record")
    if receipt.get("wall_seconds", 0) <= 0:
        fail(f"{target} receipt lacks wall time")
    text = log_path.read_text()
    theorem = "sourcePair_functions_of_chain" if target == "S4SourcePairsToFunctionsV1" else "actual_query_row31_materialized_join"
    if theorem not in text or "depends on axioms" not in text:
        fail(f"{target} log lacks theorem/axiom report")
    if any(re.search(rf"(?<![\w.]){re.escape(a)}(?![\w.])", text.split("depends on axioms:", 1)[-1]) is None for a in AXIOMS):
        fail(f"{target} log does not report the complete standard axiom set")
    if "sorryAx" in text or "Lean.ofReduceBool" in text:
        fail(f"{target} log reports a forbidden proof escape")
    source_text = source.read_text()
    if re.search(r"\b(sorry|admit)\b|\baxiom\s+", source_text):
        fail(f"{target} source contains a proof escape or custom axiom")

pins = json.loads((ROOT / "receipt/direct_import_pins.json").read_text())
if not pins:
    fail("direct import pin list is empty")
for pin in pins:
    object_path = Path(pin["selected_object"])
    if not object_path.is_file() or sha(object_path) != pin["object_sha256"]:
        fail(f"selected import object missing or changed: {pin['module']} at {object_path}")
    candidates = pin.get("candidate_sources", [])
    if not candidates:
        fail(f"source candidate hashes missing for import {pin['module']}")
    for source_pin in candidates:
        source_path = Path(source_pin["path"])
        if not source_path.is_file() or sha(source_path) != source_pin["sha256"]:
            fail(f"import source candidate missing or changed: {source_path}")

for path in ROOT.rglob("*"):
    if path.is_file() and (path.suffix in {".olean", ".ilean", ".llbc", ".bin"}):
        fail(f"compiled/binary artifact included: {path.relative_to(ROOT)}")
print("s4-query31-materialized-conditional-join packet: PASS")
