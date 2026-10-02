#!/usr/bin/env python3
"""Portable integrity and saved-run audit for R421."""
from __future__ import annotations
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent
NOTE = ROOT.parents[1] / "R421_CURRENT_MASKED31_BLOCK.md"
TARGET = ROOT.parents[1] / "lean/AspisV8R19/R421UniformMasked31Block.lean"
RUN_ID = "1790965651411147000"
EXPECTED_NAMES = [
    "AspisV8R19.R421UniformMasked31Block.masked31_value",
    "AspisV8R19.R421UniformMasked31Block.words31_value",
    "AspisV8R19.R421UniformMasked31Block.uniform_masked31_block",
]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}

def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()

def axioms(text: str) -> list[tuple[str, list[str]]]:
    pattern = re.compile(r"'([^']+)' depends on axioms: \[([\s\S]*?)\]")
    return [(name, [x.strip() for x in body.replace("\n", " ").split(",") if x.strip()])
            for name, body in pattern.findall(text)]

def main() -> None:
    manifest = json.loads((ROOT / "SHA256SUMS.json").read_text())
    expected = set(manifest["files"])
    actual = {p.relative_to(ROOT).as_posix() for p in ROOT.rglob("*")
              if p.is_file() and p.name != "SHA256SUMS.json"}
    assert actual == expected, f"inventory mismatch: missing={expected-actual}, extra={actual-expected}"
    for rel, digest in manifest["files"].items():
        assert sha(ROOT / rel) == digest, rel
    assert sha(TARGET) == sha(ROOT / "source/AspisV8R19/R421UniformMasked31Block.lean")
    run = ROOT / "runs" / RUN_ID
    assert sha(TARGET) == sha(run / "source.lean")
    receipt = json.loads((run / "receipt.json").read_text())
    log = (run / "lean.log").read_text(errors="replace")
    assert receipt["target"] == "AspisV8R19/R421UniformMasked31Block.lean"
    assert receipt["source_revision"] == "6b5f6a1274aaf7f258ee2233ebfad4eb0ce8bd76"
    assert receipt["source_sha256"] == sha(TARGET)
    assert receipt["runner_sha256"] == sha(ROOT / "run_focus.py")
    assert receipt["direct_local_import_sha256"] == {
        "AspisV8R19.R406SamplerWordDistribution":
            "b7b3aa0f3f42e39ce5945f3d4bdaad7544f2dfd39292ecf0bc26b9ea9eac1ed9"
    }
    assert receipt["resources"] == {
        "MemoryHigh": "5G", "MemoryMax": "7G", "MemorySwapMax": 0,
        "TasksMax": 128, "lean_flags": "-j1 -M4500"
    }
    assert receipt["measurement_boundary"] == "GNU time Lean-child RSS; wrapper MemoryPeak is not aggregate Lean RSS."
    wall = re.search(r"Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([^\n]+)", log)
    rss = re.search(r"Maximum resident set size \(kbytes\): (\d+)", log)
    swaps = re.search(r"Swaps: (\d+)", log)
    status = re.search(r"Exit status: (\d+)", log)
    assert wall and rss and swaps and status
    assert receipt["wall_time"] == wall.group(1) == "0:01.26"
    assert receipt["peak_rss_kib"] == int(rss.group(1)) == 3229852
    assert receipt["swaps"] == int(swaps.group(1)) == 0
    assert receipt["exit_status"] == int(status.group(1)) == 0
    reports = axioms(log)
    recorded = axioms("\n".join(receipt["complete_print_axioms"]))
    assert reports == recorded
    assert [name for name, _ in reports] == EXPECTED_NAMES
    assert all(set(ax) <= ALLOWED for _, ax in reports)
    supplemental = json.loads((ROOT / "supplemental-source-cache-audit.json").read_text())
    assert "not recorded" in supplemental["purpose"]
    assert "not a complete import-closure" in supplemental["boundary"]
    for rel, digest in supplemental["source_files"].items():
        assert sha(ROOT / "source" / rel) == digest, rel
    assert sha(ROOT / "source/AspisV8R19/R406SamplerWordDistribution.lean") == \
        receipt["direct_local_import_sha256"]["AspisV8R19.R406SamplerWordDistribution"]
    assert sha(NOTE) == manifest["external_files"]["../../R421_CURRENT_MASKED31_BLOCK.md"]
    print("R421 evidence verification: PASS")

if __name__ == "__main__":
    main()
