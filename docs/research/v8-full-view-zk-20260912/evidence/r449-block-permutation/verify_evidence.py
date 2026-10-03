#!/usr/bin/env python3
"""Read-only integrity verification for the R449 compile component."""
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

run = HERE / "run"
receipt = json.loads((run / "receipt.json").read_text())
for key in ("target", "source_revision", "source_sha256", "exit_status", "wall_time", "peak_rss_kib", "swaps"):
    require(receipt[key] == manifest[key], f"receipt {key} mismatch")
require(receipt["exit_status"] == 0 and receipt["swaps"] == 0, "run did not complete cleanly")
require(receipt["resources"] == {
    "MemoryHigh": "5G", "MemoryMax": "7G", "MemorySwapMax": 0,
    "TasksMax": 128, "flags": "-j1 -M4500"
}, "receipt resource limits mismatch")

source = DOCROOT / "lean" / manifest["target"]
require(sha(run / "source.lean") == manifest["source_sha256"], "saved compile source hash mismatch")
require(sha(source) == manifest["source_sha256"], "promoted target differs from successful source")
require(sha(HERE / "runner/run_focused_lean.py") == manifest["runner_sha256"], "runner hash mismatch")
require(sha(run / "command.json") == manifest["command_json_sha256"], "command hash mismatch")
command = json.loads((run / "command.json").read_text())
require(command[:5] == ["/home/dombarker/.elan/bin/lake", "--dir", "/home/dombarker/project-offloads/aspis-r126-release-20260930-a/focus-workspace", "env", "lean"], "saved Lean command prefix mismatch")
require("-j1" in command and "-M4500" in command and command[-1].endswith("/AspisV8R19/R449BlockPermutation.lean"), "saved Lean command target/flags mismatch")

log = (run / "lean.log").read_text()
printed = re.findall(r"'[^\n]+' (?:depends on axioms: \[[\s\S]*?\]|does not depend on any axioms)", log)
require(printed == receipt["complete_print_axioms"], "complete #print axioms output differs from receipt")
allowed = {"propext", "Classical.choice", "Quot.sound"}
for report in printed:
    found = re.search(r"depends on axioms: \[([\s\S]*?)\]$", report)
    if found:
        names = {x.strip() for x in found.group(1).replace("\n", " ").split(",")}
        require(names <= allowed, f"non-foundational axiom(s) in {report}")
require(len(printed) == 6, "expected six complete axiom reports")

gnu = (run / "gnu-time.txt").read_text()
for key, pattern in (
    ("wall_time", r"Elapsed \(wall clock\) time \(h:mm:ss or m:ss\):\s*(\S+)"),
    ("peak_rss_kib", r"Maximum resident set size \(kbytes\):\s*(\d+)"),
    ("swaps", r"Swaps:\s*(\d+)"),
):
    match = re.search(pattern, gnu)
    require(match is not None, f"GNU time output lacks {key}")
    value = match.group(1) if key == "wall_time" else int(match.group(1))
    require(value == manifest[key], f"GNU time {key} differs from manifest")
require("Exit status: 0" in gnu, "GNU time exit status mismatch")
launch_status = json.loads((run / "launch-status.json").read_text())
require(launch_status["ssh_exit_status"] == 0, "SSH launch did not return success")

prior = HERE.parent / "r447-source-initial-block-law"
for mod, entry in manifest["direct_local_import_sha256"].items():
    rel = Path(*mod.split(".")).with_suffix(".lean")
    current = DOCROOT / "lean" / rel
    saved = prior / "source" / rel
    want = entry["sha256"]
    require(sha(current) == want, f"current direct dependency changed: {mod}")
    require(sha(saved) == want, f"R447 linked source copy mismatch: {mod}")
    require(entry["path_from_lean"] == rel.as_posix(), f"dependency path mismatch: {mod}")

print("PASS: R449 source, exact command, run metrics, resources, six axiom reports, runner and linked R445/R446 sources verified")
