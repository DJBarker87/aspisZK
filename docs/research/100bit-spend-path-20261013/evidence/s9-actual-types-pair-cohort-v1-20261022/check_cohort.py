#!/usr/bin/env python3
"""Verify source/evidence hashes for the Actual→Pair field-reader cohort."""
from __future__ import annotations
import argparse, hashlib, json
from pathlib import Path

ROOT = Path(__file__).resolve().parent

def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()

def need(ok: bool, message: str) -> None:
    if not ok:
        raise SystemExit(message)

parser = argparse.ArgumentParser()
parser.add_argument("--objects", type=Path, help="optional directory containing selected compiled .olean owners")
args = parser.parse_args()
manifest = json.loads((ROOT / "COHORT-MANIFEST.json").read_text())
need(manifest.get("schema") == "focused-extractor-proof-packet-v1", "manifest schema mismatch")
need(len(manifest["stages"]) == 13, "unexpected stage count")
external = {}
for stage in manifest["stages"]:
    phase = stage["phase"]
    src = ROOT / stage["source"]
    ev = ROOT / "receipts" / phase
    receipt = json.loads((ev / "receipt.json").read_text())
    preflight = json.loads((ev / "preflight.json").read_text())
    need(src.is_file() and sha(src) == stage["source_sha256"] == receipt["source_sha256"], f"source hash mismatch: {phase}")
    need(receipt["exit_status"] == stage["exit_status"] == 0, f"accepted stage not green: {phase}")
    need(receipt["object_sha256"] == stage["object_sha256"], f"object receipt mismatch: {phase}")
    need(preflight["source_sha256"] == stage["source_sha256"], f"preflight source mismatch: {phase}")
    need(preflight["limits"]["memory.swap.max"] == "0", f"swap cap missing: {phase}")
    log = (ev / "lean.log").read_text(errors="replace")
    need("sorryAx" not in log, f"failed-proof recovery marker in accepted log: {phase}")
    need(preflight["direct_imports"] == stage["direct_imports"], f"direct import mismatch: {phase}")
    for mod, owner in stage["direct_imports"].items():
        if mod in external:
            need(external[mod]["sha256"] == owner["sha256"], f"external owner collision: {mod}")
        external[mod] = owner
    if args.objects:
        obj = args.objects / f"{stage['module']}.olean"
        need(obj.is_file() and sha(obj) == stage["object_sha256"], f"selected object absent or hash mismatch: {stage['module']}")
for failure in manifest["failed_attempts"]:
    rec = json.loads((ROOT / failure["receipt_path"]).read_text())
    need(failure["accepted"] is False and rec["exit_status"] != 0, "failed attempt misclassified")
for p in (ROOT / "tooling").iterdir():
    need(sha(p) == manifest["environment"]["tooling_sha256"][p.name], f"tooling hash mismatch: {p.name}")
need(len(external) == manifest["direct_owner_preflight"]["distinct_external_direct_import_owners"], "external owner count mismatch")
print(f"PASS: {len(manifest['stages'])} stages; {len(external)} distinct direct external owners; source and receipt hashes agree")
if args.objects:
    print("PASS: all selected .olean object hashes agree")
