#!/usr/bin/env python3
"""Read-only integrity verifier for the R452/R453 first-limb component."""
from pathlib import Path
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
DOCROOT = HERE.parent.parent


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

prior = HERE.parent / "r447-source-initial-block-law"
runner = HERE / "runner/run_focus.py"
require(sha(runner) == manifest["runner_sha256"], "shared runner hash mismatch")

good_expected = {
    "1791016838988168000": manifest["targets"][0],
    "1791017037441042000": manifest["targets"][1],
}
allowed_axioms = {"propext", "Classical.choice", "Quot.sound"}
for run_id, expected in good_expected.items():
    run = HERE / "runs" / run_id
    receipt = json.loads((run / "receipt.json").read_text())
    require(receipt["target"] == expected["target"], f"{run_id}: target mismatch")
    require(receipt["source_sha256"] == expected["source_sha256"], f"{run_id}: receipt source mismatch")
    require(sha(run / "source.lean") == expected["source_sha256"], f"{run_id}: saved source mismatch")
    target = DOCROOT / "lean" / receipt["target"]
    require(sha(target) == expected["source_sha256"], f"{run_id}: promoted target differs")
    for key in ("exit_status", "wall_time", "peak_rss_kib", "swaps"):
        require(receipt[key] == expected[key], f"{run_id}: {key} mismatch")
    require(receipt["exit_status"] == 0 and receipt["swaps"] == 0, f"{run_id}: run not successful")
    limits = receipt["resources"]
    require(limits == {"MemoryHigh": "5G", "MemoryMax": "7G", "MemorySwapMax": 0, "TasksMax": 128, "lean_flags": "-j1 -M4500"}, f"{run_id}: resource limits mismatch")
    log = (run / "lean.log").read_text()
    reports = re.findall(r"'[^\n]+' (?:depends on axioms: \[[\s\S]*?\]|does not depend on any axioms)", log)
    require(reports == receipt["complete_print_axioms"] == expected["axioms"], f"{run_id}: axiom report mismatch")
    for report in reports:
        found = re.search(r"depends on axioms: \[([\s\S]*?)\]$", report)
        if found:
            names = {x.strip() for x in found.group(1).replace("\n", " ").split(",")}
            require(names <= allowed_axioms, f"{run_id}: unexpected axiom {names - allowed_axioms}")
    for imp, want in expected["direct_import_sha256"].items():
        rel = Path(*imp.split(".")).with_suffix(".lean")
        require(sha(DOCROOT / "lean" / rel) == want, f"{run_id}: current dependency {imp} hash mismatch")
        if imp == "AspisV8R19.R452NoRefillProgram":
            linked = HERE / "runs/1791016838988168000/source.lean"
        else:
            linked = prior / "source" / rel
        require(sha(linked) == want, f"{run_id}: linked dependency {imp} mismatch")
    if run_id == "1791016838988168000":
        command = (run / "command.txt").read_text().rstrip("\n")
        rawlog = log
        match = re.search(r'Command being timed: "([^"]+)"', rawlog)
        require(match is not None and match.group(1) == command, f"{run_id}: command capture mismatch")
    else:
        command = (run / "command.txt").read_text().rstrip("\n")
        match = re.search(r'Command being timed: "([^"]+)"', log)
        require(match is not None and match.group(1) == command, f"{run_id}: command capture mismatch")
    for key, pattern in (
        ("wall_time", r"Elapsed \(wall clock\) time \(h:mm:ss or m:ss\):\s*(\S+)"),
        ("peak_rss_kib", r"Maximum resident set size \(kbytes\):\s*(\d+)"),
        ("swaps", r"Swaps:\s*(\d+)"),
    ):
        match = re.search(pattern, log)
        require(match is not None, f"{run_id}: GNU output lacks {key}")
        value = match.group(1) if key == "wall_time" else int(match.group(1))
        require(value == expected[key], f"{run_id}: GNU {key} mismatch")
    require("Exit status: 0" in log, f"{run_id}: GNU exit status mismatch")

history = {r["run_id"]: r for r in manifest["run_history"]}
require(set(history) == {"1791016803795709000", "1791016838988168000", "1791016921295247000", "1791016969555617000", "1791017037441042000"}, "run history inventory mismatch")
for run_id, record in history.items():
    run = HERE / "runs" / run_id
    receipt = json.loads((run / "receipt.json").read_text())
    require(receipt["exit_status"] == record["exit_status"], f"{run_id}: history status mismatch")
    require(sha(run / "source.lean") == record["source_sha256"], f"{run_id}: history source hash mismatch")
    require(sha(run / "receipt.json") == record["receipt_sha256"], f"{run_id}: history receipt hash mismatch")
    require(receipt["target"] == record["target"], f"{run_id}: history target mismatch")
    if run_id not in good_expected:
        require(record["label"].startswith(("rejected-", "superseded-")), f"{run_id}: history disposition missing")

print("PASS: R452/R453 source snapshots, promoted targets, direct imports, exact commands, resources, GNU metrics, complete axiom reports, linked R447 dependencies and preserved history verified")
