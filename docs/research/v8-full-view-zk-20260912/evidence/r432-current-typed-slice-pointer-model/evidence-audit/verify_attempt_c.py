#!/usr/bin/env python3
"""Read-only consistency check for saved R432 attempt C evidence."""
from __future__ import annotations

import hashlib
import json
import pathlib
import re

ROOT = pathlib.Path(__file__).resolve().parents[1]
RUN = ROOT / "attempt-c"


def load(name: str):
    return json.loads((RUN / name).read_text())


def digest(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


receipt = load("receipt.json")
source = RUN / "source.lean"
source_hash = digest(source)
source_text = source.read_text()
assert receipt["target"] == "AspisV8R19/R432PointerPrimitive.lean"
assert receipt["exit_status"] == 0
assert receipt["source_sha256"] == source_hash
assert receipt["source_revision"] == "cacf6c885a3beffc89fd6be7e8f3801cd8786d2e"
assert receipt["lean_version"].startswith("Lean (version 4.32.0,")

command = load("command.json")
assert command[-1] == "/home/dombarker/project-offloads/aspis-r57-lean-src-20260929-a/AspisV8R19/R432PointerPrimitive.lean"
assert command[command.index("-j1")] == "-j1"
assert command[command.index("-M4500")] == "-M4500"
assert load("launch-status.json")["ssh_exit_status"] == 0

before = load("host-before.json")
after = load("host-after.json")
expected_limits = {
    "memory.high": "5368709120",
    "memory.max": "7516192768",
    "memory.swap.max": "0",
    "pids.max": "128",
}
for snap in (before, after):
    for name, expected in expected_limits.items():
        assert snap["cgroup"][name] == expected, (name, snap["cgroup"].get(name))
    assert snap["cgroup"]["memory.events"].splitlines()[-3:] == [
        "oom 0",
        "oom_kill 0",
        "oom_group_kill 0",
    ]
assert after["source_sha256"] == source_hash
assert before["lean_version"] == receipt["lean_version"]
assert after["olean_sha256"]

gnu = (RUN / "gnu-time.txt").read_text()
wall = re.search(r"Elapsed \(wall clock\) time \(h:mm:ss or m:ss\):\s*(\S+)", gnu)
rss = re.search(r"Maximum resident set size \(kbytes\):\s*(\d+)", gnu)
swaps = re.search(r"Swaps:\s*(\d+)", gnu)
status = re.search(r"Exit status:\s*(\d+)", gnu)
assert wall and rss and swaps and status
assert wall.group(1) == receipt["wall_time"]
assert int(rss.group(1)) == receipt["peak_rss_kib"]
assert int(swaps.group(1)) == receipt["swaps"] == 0
assert int(status.group(1)) == receipt["exit_status"] == 0

printed = [line.strip() for line in (RUN / "lean.log").read_text().splitlines() if "depends on axioms:" in line]
assert printed == receipt["complete_print_axioms"]
assert len(printed) == 12
assert source_text.count("#print axioms ") == len(printed)
allowed = {"propext", "Classical.choice", "Quot.sound"}
for line in printed:
    axiom_text = line.split("depends on axioms: [", 1)[1].rsplit("]", 1)[0]
    assert set(map(str.strip, axiom_text.split(","))) <= allowed
assert all("sorryAx" not in line for line in printed)

copy_status = sorted(p.name for p in RUN.glob("*.copy-status.json"))
copy_failures = []
for name in copy_status:
    data = json.loads((RUN / name).read_text())
    if data.get("exit_status") != 0:
        copy_failures.append(name)
assert copy_status and not copy_failures, (copy_status, copy_failures)

report = {
    "status": "PASS",
    "source_sha256": source_hash,
    "target": receipt["target"],
    "source_revision": receipt["source_revision"],
    "exit_status": receipt["exit_status"],
    "wall_time": receipt["wall_time"],
    "gnu_peak_rss_kib": receipt["peak_rss_kib"],
    "swaps": receipt["swaps"],
    "axiom_report_count": len(printed),
    "axiom_whitelist": sorted(allowed),
    "effective_cgroup_limits": expected_limits,
    "copy_status_files": copy_status,
    "gnu_rss_and_cgroup_peak_reported_independently": {
        "gnu_max_rss_kib": int(rss.group(1)),
        "cgroup_memory_peak_bytes": int(after["cgroup"]["memory.peak"]),
    },
}
report_path = pathlib.Path(__file__).resolve().parent / "audit-report.json"
report_path.write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps(report, indent=2))
