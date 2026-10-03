#!/usr/bin/env python3
"""Read-only integrity verifier for the R454/R455 refill component."""
from pathlib import Path
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
DOCROOT = HERE.parent.parent
PREVIOUS = HERE.parent / "r453-source-first-limb-law"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(ok, message):
    if not ok:
        raise SystemExit("FAIL: " + message)


manifest = json.loads((HERE / "manifest.json").read_text())
listed = {}
for line in (HERE / "SHA256SUMS").read_text().splitlines():
    digest, rel = line.split("  ", 1)
    listed[rel] = digest
actual = {
    path.relative_to(HERE).as_posix(): sha(path)
    for path in HERE.rglob("*")
    if path.is_file() and path.name != "SHA256SUMS"
}
require(listed == actual, "SHA256SUMS differs from component files")
require(sha(HERE / "runner/run_focus.py") == manifest["runner_sha256"], "runner hash mismatch")

good = {t["run_id"]: t for t in manifest["targets"]}
allowed = {"propext", "Classical.choice", "Quot.sound"}
for run_id, target in good.items():
    run = HERE / "runs" / run_id
    receipt = json.loads((run / "receipt.json").read_text())
    for key in ("target", "source_revision", "source_sha256", "exit_status", "wall_time", "peak_rss_kib", "swaps"):
        expected_key = "source_sha256" if key == "source_sha256" else key
        require(receipt[key] == target[expected_key], f"{run_id}: {key} mismatch")
    require(receipt["exit_status"] == 0 and receipt["swaps"] == 0, f"{run_id}: unsuccessful run")
    require(receipt["resources"] == {"MemoryHigh": "5G", "MemoryMax": "7G", "MemorySwapMax": 0, "TasksMax": 128, "lean_flags": "-j1 -M4500"}, f"{run_id}: limits mismatch")
    source = run / "source.lean"
    require(sha(source) == target["source_sha256"], f"{run_id}: saved source hash mismatch")
    require(sha(DOCROOT / "lean" / target["target"]) == target["source_sha256"], f"{run_id}: promoted source differs")
    log = (run / "lean.log").read_text()
    reports = re.findall(r"'[^\n]+' (?:depends on axioms: \[[\s\S]*?\]|does not depend on any axioms)", log)
    require(reports == receipt["complete_print_axioms"] == target["complete_print_axioms"], f"{run_id}: complete axiom output mismatch")
    for report in reports:
        match = re.search(r"depends on axioms: \[([\s\S]*?)\]$", report)
        if match:
            names = {x.strip() for x in match.group(1).replace("\n", " ").split(",")}
            require(names <= allowed, f"{run_id}: non-foundational axiom(s): {names - allowed}")
    cmd = (run / "command.txt").read_text().rstrip("\n")
    match = re.search(r'Command being timed: "([^"]+)"', log)
    require(match is not None and match.group(1) == cmd, f"{run_id}: command mismatch")
    for key, pattern in (
        ("wall_time", r"Elapsed \(wall clock\) time \(h:mm:ss or m:ss\):\s*(\S+)"),
        ("peak_rss_kib", r"Maximum resident set size \(kbytes\):\s*(\d+)"),
        ("swaps", r"Swaps:\s*(\d+)"),
    ):
        match = re.search(pattern, log)
        require(match is not None, f"{run_id}: GNU time lacks {key}")
        value = match.group(1) if key == "wall_time" else int(match.group(1))
        require(value == target[key], f"{run_id}: GNU {key} mismatch")
    require("Exit status: 0" in log, f"{run_id}: GNU exit status mismatch")
    for imp, want in target["direct_import_sha256"].items():
        rel = Path(*imp.split(".")).with_suffix(".lean")
        require(sha(DOCROOT / "lean" / rel) == want, f"{run_id}: current import mismatch: {imp}")
        if imp == "AspisV8R19.R454RefillProgramShape":
            saved = HERE / "runs/1791017319125748000/source.lean"
        elif imp == "AspisV8R19.R452NoRefillProgram":
            saved = PREVIOUS / "runs/1791016838988168000/source.lean"
        else:
            saved = PREVIOUS / "runs/1791017037441042000/source.lean"
        require(sha(saved) == want, f"{run_id}: linked import mismatch: {imp}")

for record in manifest["run_history"]:
    run_id = record["run_id"]
    run = HERE / "runs" / run_id
    receipt = json.loads((run / "receipt.json").read_text())
    require(receipt["target"] == record["target"], f"{run_id}: history target mismatch")
    require(receipt["source_sha256"] == record["source_sha256"] == sha(run / "source.lean"), f"{run_id}: history source mismatch")
    require(receipt["exit_status"] == record["exit_status"], f"{run_id}: history status mismatch")
    require(sha(run / "receipt.json") == record["receipt_sha256"], f"{run_id}: history receipt mismatch")

print("PASS: R454/R455 sources, imports, exact commands, caps, GNU metrics, full axiom reports, and retained draft history verified")
