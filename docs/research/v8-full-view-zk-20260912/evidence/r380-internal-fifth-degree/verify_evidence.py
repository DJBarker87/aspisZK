#!/usr/bin/env python3
"""Read-only, checksum-complete verifier for the saved R380 evidence."""
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent
PROJECT = ROOT.parents[4]
MODULE = ROOT / "promoted-source/R380InternalFifthDegree.lean"
TRACKED = PROJECT / "docs/research/v8-full-view-zk-20260912/lean/AspisV8R19/R380InternalFifthDegree.lean"
RUN_IDS = ["1790952289292760000", "1790952545664319000"]
EXPECTED_TARGETS = ["R380InternalFifthDegree.lean", "AspisV8R19/R380InternalFifthDegree.lean"]
EXPECTED_AXIOMS = ["propext", "Classical.choice", "Quot.sound"]
EXPECTED_THEOREMS = [
    "AspisR19.R380InternalFifthDegree.internalRound_degree",
    "AspisR19.R380InternalFifthDegree.two_internalRounds_degree",
]
EXPECTED_CAPS = {"MemoryHigh":"5G", "MemoryMax":"7G", "MemorySwapMax":0,
                 "TasksMax":128, "lean_flags":"-j1 -M4500"}


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()

# The checksum manifest must cover exactly every file in the evidence bundle except itself.
checksum_rows = {}
for line in (ROOT / "SHA256SUMS").read_text().splitlines():
    digest, rel = line.split("  ", 1)
    rel = Path(rel).as_posix().removeprefix("./")
    assert rel not in checksum_rows and not rel.startswith("/") and ".." not in Path(rel).parts
    checksum_rows[rel] = digest
    assert sha(ROOT / rel) == digest, f"evidence checksum mismatch: {rel}"
actual_files = {p.relative_to(ROOT).as_posix() for p in ROOT.rglob("*") if p.is_file() and p.name != "SHA256SUMS"}
assert set(checksum_rows) == actual_files, "SHA256SUMS is incomplete or includes stale paths"

assert MODULE.read_bytes() == TRACKED.read_bytes(), "tracked module differs from promotion copy"
meta = json.loads((ROOT / "inventory.json").read_text())
assert sha(MODULE) == meta["module_sha256"]
assert meta["bundle_files"] == sorted(actual_files), "inventory does not enumerate the complete bundle"
source = MODULE.read_text()
assert "import AspisV8R19.R378PairedFifthDegree" in source
for theorem in ["internalRound_degree", "two_internalRounds_degree"]:
    assert f"#print axioms {theorem}" in source

# Imported declaration provenance must match both the current promoted file and bundled copy.
dep_rel = "docs/research/v8-full-view-zk-20260912/lean/AspisV8R19/R378PairedFifthDegree.lean"
dep = PROJECT / dep_rel
bundled_dep = ROOT / "source-route/promoted-imports/AspisV8R19/R378PairedFifthDegree.lean"
expected_dep = meta["direct_imports"]["AspisV8R19.R378PairedFifthDegree"]
assert sha(dep) == sha(bundled_dep) == expected_dep

assert len(meta["runs"]) == len(RUN_IDS)
runner = (ROOT / "runner/run_focus.py").read_text()
assert sha(ROOT / "runner/run_focus.py") == meta["runner_sha256"]
for required in ["MemoryHigh=5G", "MemoryMax=7G", "MemorySwapMax=0", "TasksMax=128", "-j1", "-M4500"]:
    assert required in runner, f"runner does not encode required cap/flag: {required}"
for idx, (run_id, expected_target) in enumerate(zip(RUN_IDS, EXPECTED_TARGETS)):
    prefix = ROOT / "runs" / f"aspis-focus-{run_id}"
    receipt = json.loads(prefix.with_suffix(".receipt.json").read_text())
    log_path = prefix.with_suffix(".log")
    snapshot = prefix.with_suffix(".source.lean")
    log = log_path.read_text()
    row = meta["runs"][idx]
    assert receipt["target"] == expected_target == row["target"]
    assert receipt["source_revision"] == row["source_revision"]
    assert receipt["exit_status"] == row["exit_status"] == 0
    assert receipt["source_sha256"] == row["source_sha256"] == sha(snapshot) == sha(MODULE)
    assert receipt["runner_sha256"] == row["runner_sha256"] == meta["runner_sha256"]
    assert receipt["direct_local_import_sha256"] == row["direct_local_import_sha256"] == meta["direct_imports"]
    assert receipt["resources"] == row["resources"] == EXPECTED_CAPS
    assert receipt["wall_time"] == row["wall_time"]
    assert receipt["peak_rss_kib"] == row["peak_rss_kib"]
    assert receipt["swaps"] == row["swaps"] == 0
    assert receipt["complete_print_axioms"] == row["complete_print_axioms"]
    assert log_path.is_file()

    # Cross-check receipt fields against the raw GNU-time/systemd log.
    wall = re.search(r"Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): (\S+)", log)
    rss = re.search(r"Maximum resident set size \(kbytes\): (\d+)", log)
    swap = re.search(r"Swaps: (\d+)", log)
    status = re.search(r"^\s*Exit status: (\d+)\s*$", log, re.M)
    assert wall and wall.group(1) == receipt["wall_time"]
    assert rss and int(rss.group(1)) == receipt["peak_rss_kib"]
    assert swap and int(swap.group(1)) == receipt["swaps"] == 0
    assert status and int(status.group(1)) == receipt["exit_status"]
    assert "-j1 -M4500" in log
    assert "Memory swap peak: 0B" in log
    wrapper_peak = re.search(r"^\s*Memory peak: (\S+)\s*$", log, re.M)
    assert wrapper_peak, "missing systemd wrapper peak measurement"
    expected_olean = "AspisV8R19/R380InternalFifthDegree.olean" if idx else "/R380InternalFifthDegree.olean"
    assert expected_olean in log

    # Raw output, receipt, manifest and exact whitelist must agree on all complete axioms reports.
    raw_axioms = [line for line in log.splitlines() if line.startswith("'AspisR19.R380InternalFifthDegree.") and "depends on axioms:" in line]
    reports = receipt["complete_print_axioms"]
    assert raw_axioms == reports == row["complete_print_axioms"]
    assert [line.split("'", 2)[1] for line in raw_axioms] == EXPECTED_THEOREMS
    for line in raw_axioms:
        axiom_text = line.split("depends on axioms: ", 1)[1]
        assert axiom_text == "[propext, Classical.choice, Quot.sound]"
        assert "sorryAx" not in line

print(json.dumps({"status":"PASS", "module_sha256":sha(MODULE), "run_ids":RUN_IDS,
                  "theorems":EXPECTED_THEOREMS, "axioms":EXPECTED_AXIOMS,
                  "bundle_files_checked":len(actual_files)}, indent=2))
