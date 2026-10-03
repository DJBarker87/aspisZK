#!/usr/bin/env python3
"""Read-only integrity verifier for the R459–R463 indexed block component."""
from pathlib import Path
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
DOCROOT = HERE.parent.parent
EVIDENCE = DOCROOT / "evidence"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def need(ok, message):
    if not ok:
        raise SystemExit("FAIL: " + message)


manifest = json.loads((HERE / "manifest.json").read_text())
listed = {}
for line in (HERE / "SHA256SUMS").read_text().splitlines():
    digest, rel = line.split("  ", 1)
    listed[rel] = digest
actual = {p.relative_to(HERE).as_posix(): sha(p) for p in HERE.rglob("*") if p.is_file() and p.name != "SHA256SUMS"}
need(listed == actual, "SHA256SUMS mismatch")
need(sha(HERE / "runner/run_focus.py") == manifest["runner_sha256"], "runner hash mismatch")

linked = {
    "AspisV8R19.R456IndexedWordPermutation": EVIDENCE / "r458-indexed-tape-scan-component/runs/1791018094270034000/source.lean",
    "AspisV8R19.R443BoundedRejectionMass": EVIDENCE / "r447-source-initial-block-law/source/AspisV8R19/R443BoundedRejectionMass.lean",
    "AspisV8R19.R451BlockStoppingCore": EVIDENCE / "r450-r451-refill-permutation-coupling/runs/1791017070604411000/source.lean",
    "AspisV8R19.R459IndexedFiniteTape": HERE / "runs/1791018365903250000/source.lean",
    "AspisV8R19.R461OptionScanCount": HERE / "runs/1791018575183702000/source.lean",
    "AspisV8R19.R457IndexedScan": EVIDENCE / "r458-indexed-tape-scan-component/runs/1791018165731117000/source.lean",
    "AspisV8R19.R447SourceInitialBlockLaw": EVIDENCE / "r447-source-initial-block-law/source/AspisV8R19/R447SourceInitialBlockLaw.lean",
    "AspisV8R19.R448RefillSourceLimb": EVIDENCE / "r448-refill-source-limb/run/source.lean",
}
allowed = {"propext", "Classical.choice", "Quot.sound"}
for rec in manifest["targets"]:
    rid = rec["run_id"]
    run = HERE / "runs" / rid
    receipt = json.loads((run / "receipt.json").read_text())
    for key in ("target", "source_revision", "source_sha256", "exit_status", "wall_time", "peak_rss_kib", "swaps"):
        need(receipt[key] == rec[key], f"{rid}: receipt {key} mismatch")
    need(receipt["exit_status"] == 0 and rec["swaps"] == 0, f"{rid}: run did not succeed without swap")
    need(receipt["resources"] == {"MemoryHigh":"5G","MemoryMax":"7G","MemorySwapMax":0,"TasksMax":128,"lean_flags":"-j1 -M4500"}, f"{rid}: caps mismatch")
    need(sha(run / "source.lean") == rec["source_sha256"], f"{rid}: source snapshot mismatch")
    need(sha(DOCROOT / "lean" / rec["target"]) == rec["source_sha256"], f"{rid}: promoted target mismatch")
    log = (run / "lean.log").read_text()
    reports = re.findall(r"'[^\n]+' (?:depends on axioms: \[[\s\S]*?\]|does not depend on any axioms)", log)
    need(reports == receipt["complete_print_axioms"] == rec["complete_print_axioms"], f"{rid}: full axiom report mismatch")
    for report in reports:
        match = re.search(r"depends on axioms: \[([\s\S]*?)\]$", report)
        if match:
            names = {x.strip() for x in match.group(1).replace("\n", " ").split(",")}
            need(names <= allowed, f"{rid}: unexpected axiom(s): {names - allowed}")
    command = (run / "command.txt").read_text().rstrip("\n")
    match = re.search(r'Command being timed: "([^"]+)"', log)
    need(match is not None and match.group(1) == command, f"{rid}: exact command mismatch")
    for key, pattern in (
        ("wall_time", r"Elapsed \(wall clock\) time \(h:mm:ss or m:ss\):\s*(\S+)"),
        ("peak_rss_kib", r"Maximum resident set size \(kbytes\):\s*(\d+)"),
        ("swaps", r"Swaps:\s*(\d+)"),
    ):
        match = re.search(pattern, log)
        need(match is not None, f"{rid}: GNU time lacks {key}")
        value = match.group(1) if key == "wall_time" else int(match.group(1))
        need(value == rec[key], f"{rid}: GNU {key} mismatch")
    need("Exit status: 0" in log, f"{rid}: GNU exit status mismatch")
    for imp, digest in rec["direct_import_sha256"].items():
        need(imp in linked, f"{rid}: unclassified import {imp}")
        current = DOCROOT / "lean" / Path(*imp.split(".")).with_suffix(".lean")
        need(sha(current) == digest, f"{rid}: promoted dependency hash mismatch: {imp}")
        need(sha(linked[imp]) == digest, f"{rid}: linked dependency hash mismatch: {imp}")

for rec in manifest["rejected_or_superseded_history"]:
    rid = rec["run_id"]
    run = HERE / "runs" / rid
    receipt = json.loads((run / "receipt.json").read_text())
    need(receipt["target"] == rec["target"], f"{rid}: history target mismatch")
    need(receipt["source_sha256"] == rec["source_sha256"] == sha(run / "source.lean"), f"{rid}: history source mismatch")
    need(receipt["exit_status"] == rec["exit_status"], f"{rid}: history status mismatch")
    need(receipt["wall_time"] == rec["wall_time"] and receipt["peak_rss_kib"] == rec["peak_rss_kib"] and receipt["swaps"] == rec["swaps"], f"{rid}: history metrics mismatch")
    need(sha(run / "receipt.json") == rec["receipt_sha256"], f"{rid}: history receipt hash mismatch")
    if rec["label"].startswith("rejected-"):
        need(rec["exit_status"] == 1, f"{rid}: rejected run status should be nonzero")
    if "unqualified" in rec["label"]:
        need(rec.get("receipt_target", "").startswith("docs/"), f"{rid}: unqualified module-target history is not identified")

print("PASS: R459–R463 promoted sources, exact run commands, caps, metrics, foundational axioms, linked dependencies, and rejected/superseded histories verified")
