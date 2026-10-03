#!/usr/bin/env python3
"""Read-only integrity verification for the R456–R458 component."""
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
    "AspisV8R19.R444InitialSourceLimb": EVIDENCE / "r447-source-initial-block-law/source/AspisV8R19/R444InitialSourceLimb.lean",
    "AspisV8R19.R449BlockPermutation": EVIDENCE / "r449-block-permutation/run/source.lean",
    "AspisV8R19.R456IndexedWordPermutation": HERE / "runs/1791018094270034000/source.lean",
}
allowed = {"propext", "Classical.choice", "Quot.sound"}
for rec in manifest["targets"]:
    rid = rec["run_id"]
    run = HERE / "runs" / rid
    receipt = json.loads((run / "receipt.json").read_text())
    need(receipt["target"] == rec.get("receipt_target", rec["target"]), f"{rid}: receipt target mismatch")
    for key in ("source_revision", "source_sha256", "exit_status", "wall_time", "peak_rss_kib", "swaps"):
        need(receipt[key] == rec[key], f"{rid}: receipt {key} mismatch")
    need(receipt["exit_status"] == 0 and receipt["swaps"] == 0, f"{rid}: unsuccessful run")
    need(receipt["resources"] == {"MemoryHigh":"5G","MemoryMax":"7G","MemorySwapMax":0,"TasksMax":128,"lean_flags":"-j1 -M4500"}, f"{rid}: caps mismatch")
    need(sha(run / "source.lean") == rec["source_sha256"], f"{rid}: source snapshot mismatch")
    need(sha(DOCROOT / "lean" / rec["target"]) == rec["source_sha256"], f"{rid}: promoted target mismatch")
    log = (run / "lean.log").read_text()
    reports = re.findall(r"'[^\n]+' (?:depends on axioms: \[[\s\S]*?\]|does not depend on any axioms)", log)
    need(reports == rec["complete_print_axioms"] == receipt["complete_print_axioms"], f"{rid}: complete axiom reports mismatch")
    for report in reports:
        m = re.search(r"depends on axioms: \[([\s\S]*?)\]$", report)
        if m:
            names = {x.strip() for x in m.group(1).replace("\n", " ").split(",")}
            need(names <= allowed, f"{rid}: unexpected axiom(s): {names - allowed}")
    command = (run / "command.txt").read_text().rstrip("\n")
    m = re.search(r'Command being timed: "([^"]+)"', log)
    need(m is not None and m.group(1) == command, f"{rid}: exact command mismatch")
    for key, pattern in (
        ("wall_time", r"Elapsed \(wall clock\) time \(h:mm:ss or m:ss\):\s*(\S+)"),
        ("peak_rss_kib", r"Maximum resident set size \(kbytes\):\s*(\d+)"),
        ("swaps", r"Swaps:\s*(\d+)"),
    ):
        m = re.search(pattern, log)
        need(m is not None, f"{rid}: GNU time missing {key}")
        val = m.group(1) if key == "wall_time" else int(m.group(1))
        need(val == rec[key], f"{rid}: GNU {key} mismatch")
    need("Exit status: 0" in log, f"{rid}: GNU exit mismatch")
    for imp, digest in rec["direct_import_sha256"].items():
        need(imp in linked, f"{rid}: unclassified direct import {imp}")
        path = DOCROOT / "lean" / Path(*imp.split(".")).with_suffix(".lean")
        need(sha(path) == digest, f"{rid}: current direct import {imp} mismatch")
        need(sha(linked[imp]) == digest, f"{rid}: linked direct import {imp} mismatch")

for sup in manifest["superseded_history"]:
    run = HERE / "runs" / sup["run_id"]
    receipt = json.loads((run / "receipt.json").read_text())
    need(receipt["exit_status"] == sup["exit_status"] == 0, f"{sup['run_id']}: superseded compile status mismatch")
    need(receipt["target"] == sup["receipt_target"], f"{sup['run_id']}: superseded target identity mismatch")
    need(receipt["source_sha256"] == sup["source_sha256"] == sha(run / "source.lean"), f"{sup['run_id']}: superseded source mismatch")
    need(sup["source_sha256"] != manifest["targets"][0]["source_sha256"] or "module-identity" in sup["label"], f"{sup['run_id']}: superseded disposition missing")
    need(sup["label"].startswith("superseded-"), f"{sup['run_id']}: superseded disposition missing")
    need(sha(run / "receipt.json") == sup["receipt_sha256"], f"{sup['run_id']}: superseded receipt hash mismatch")

print("PASS: R456–R458 sources, direct links, run commands, caps, metrics, axioms, and superseded R456 history verified")
