#!/usr/bin/env python3
"""Read-only integrity verifier for the R450/R451 component."""
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
actual = {
    p.relative_to(HERE).as_posix(): sha(p)
    for p in HERE.rglob("*")
    if p.is_file() and p.name != "SHA256SUMS"
}
need(listed == actual, "SHA256SUMS mismatch")
need(sha(HERE / "runner/run_focus.py") == manifest["runner_sha256"], "runner hash mismatch")

successful = {r["run_id"]: r for r in manifest["targets"]}
allowed = {"propext", "Classical.choice", "Quot.sound"}
links = {
    "AspisV8R19.R444InitialSourceLimb": EVIDENCE / "r447-source-initial-block-law/source/AspisV8R19/R444InitialSourceLimb.lean",
    "AspisV8R19.R447SourceInitialBlockLaw": EVIDENCE / "r447-source-initial-block-law/source/AspisV8R19/R447SourceInitialBlockLaw.lean",
    "AspisV8R19.R448RefillSourceLimb": EVIDENCE / "r448-refill-source-limb/run/source.lean",
    "AspisV8R19.R449BlockPermutation": EVIDENCE / "r449-block-permutation/run/source.lean",
    "AspisV8R19.R451BlockStoppingCore": HERE / "runs/1791017070604411000/source.lean",
    "AspisV8R19.R451BlockStoppingPermutation": HERE / "runs/1791017557672302000/source.lean",
}
for run_id, rec in successful.items():
    run = HERE / "runs" / run_id
    receipt = json.loads((run / "receipt.json").read_text())
    for key in ("target", "source_revision", "source_sha256", "exit_status", "wall_time", "peak_rss_kib", "swaps"):
        need(receipt[key] == rec[key], f"{run_id}: {key} differs from manifest")
    need(receipt["exit_status"] == 0 and receipt["swaps"] == 0, f"{run_id}: run unsuccessful")
    need(receipt["resources"] == {"MemoryHigh":"5G","MemoryMax":"7G","MemorySwapMax":0,"TasksMax":128,"lean_flags":"-j1 -M4500"}, f"{run_id}: limits mismatch")
    source = run / "source.lean"
    need(sha(source) == rec["source_sha256"], f"{run_id}: run source mismatch")
    need(sha(DOCROOT / "lean" / rec["target"]) == rec["source_sha256"], f"{run_id}: promoted target mismatch")
    log = (run / "lean.log").read_text()
    reports = re.findall(r"'[^\n]+' (?:depends on axioms: \[[\s\S]*?\]|does not depend on any axioms)", log)
    need(reports == receipt["complete_print_axioms"] == rec["complete_print_axioms"], f"{run_id}: axiom reports mismatch")
    for report in reports:
        match = re.search(r"depends on axioms: \[([\s\S]*?)\]$", report)
        if match:
            names = {x.strip() for x in match.group(1).replace("\n", " ").split(",")}
            need(names <= allowed, f"{run_id}: unexpected axiom(s): {names - allowed}")
    command = (run / "command.txt").read_text().rstrip("\n")
    match = re.search(r'Command being timed: "([^"]+)"', log)
    need(match is not None and match.group(1) == command, f"{run_id}: exact command mismatch")
    for key, pattern in (
        ("wall_time", r"Elapsed \(wall clock\) time \(h:mm:ss or m:ss\):\s*(\S+)"),
        ("peak_rss_kib", r"Maximum resident set size \(kbytes\):\s*(\d+)"),
        ("swaps", r"Swaps:\s*(\d+)"),
    ):
        match = re.search(pattern, log)
        need(match is not None, f"{run_id}: GNU time missing {key}")
        val = match.group(1) if key == "wall_time" else int(match.group(1))
        need(val == rec[key], f"{run_id}: GNU {key} mismatch")
    need("Exit status: 0" in log, f"{run_id}: GNU exit status mismatch")
    for imp, want in rec["direct_import_sha256"].items():
        need(imp in links, f"{run_id}: unclassified import {imp}")
        local = DOCROOT / "lean" / Path(*imp.split(".")).with_suffix(".lean")
        need(sha(local) == want, f"{run_id}: current imported source mismatch {imp}")
        need(sha(links[imp]) == want, f"{run_id}: linked imported source mismatch {imp}")

for rec in manifest["run_history"]:
    run_id = rec["run_id"]
    run = HERE / "runs" / run_id
    receipt = json.loads((run / "receipt.json").read_text())
    need(receipt["source_sha256"] == rec["source_sha256"] == sha(run / "source.lean"), f"{run_id}: rejected source mismatch")
    need(receipt["exit_status"] == rec["exit_status"] == 1, f"{run_id}: rejected run status mismatch")
    need(sha(run / "receipt.json") == rec["receipt_sha256"], f"{run_id}: rejected receipt mismatch")
    need(receipt["resources"] == {"MemoryHigh":"5G","MemoryMax":"7G","MemorySwapMax":0,"TasksMax":128,"lean_flags":"-j1 -M4500"}, f"{run_id}: rejected run limits mismatch")
    log = (run / "lean.log").read_text()
    need("kernel) excessive memory consumption detected" in log, f"{run_id}: expected excessive-memory failure absent")
    peak = re.search(r"Maximum resident set size \(kbytes\):\s*(\d+)", log)
    swaps = re.search(r"Swaps:\s*(\d+)", log)
    need(peak is not None and int(peak.group(1)) == rec["peak_rss_kib"], f"{run_id}: rejected GNU peak mismatch")
    need(swaps is not None and int(swaps.group(1)) == 0 and "Exit status: 1" in log, f"{run_id}: rejected GNU status/swaps mismatch")

print("PASS: R450/R451 promoted sources, direct dependency links, exact successful commands, caps, GNU metrics, foundational axioms, and preserved unchanged-cap excessive-memory failures verified")
