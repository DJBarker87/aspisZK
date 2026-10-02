#!/usr/bin/env python3
"""Portable integrity, resource-receipt, and axiom audit for R412."""
from __future__ import annotations
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent
NOTE = ROOT.parents[1] / "R412_CURRENT_LEGAL_QUERY_ENUMERATION.md"
TARGET = ROOT.parents[1] / "lean/AspisV8R19/R412LegalQueryEnumeration.lean"
GREEN = "1790964302904773000"
FAILED = ("1790964238281487000", "1790964273120393000")
EXPECTED_NAMES = [
    "AspisV8R19.R412LegalQueryEnumeration.enumQuery_injective",
    "AspisV8R19.R412LegalQueryEnumeration.listQuery_injective",
    "AspisV8R19.R412LegalQueryEnumeration.enum_legalOfList",
    "AspisV8R19.R412LegalQueryEnumeration.existsUnique_enumQuery",
    "AspisV8R19.R412LegalQueryEnumeration.test_eq_legal_sum",
]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}

def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()

def run_files(run_id: str) -> tuple[Path, Path, Path]:
    d = ROOT / "runs" / run_id
    return d / "source.lean", d / "lean.log", d / "receipt.json"

def axioms_from_log(log: str) -> list[tuple[str, list[str]]]:
    pattern = re.compile(r"'([^']+)' depends on axioms: \[([\s\S]*?)\]")
    out = []
    for name, body in pattern.findall(log):
        axioms = [x.strip() for x in body.replace("\n", " ").split(",") if x.strip()]
        out.append((name, axioms))
    return out

def check_run(run_id: str, *, green: bool) -> None:
    source, log_path, receipt_path = run_files(run_id)
    receipt = json.loads(receipt_path.read_text())
    log = log_path.read_text(errors="replace")
    assert receipt["target"] == "AspisV8R19/R412LegalQueryEnumeration.lean"
    assert receipt["source_revision"] == "c145fb14be60e3b2553713927228ac62876dbab2"
    assert receipt["runner_sha256"] == sha(ROOT / "run_focus.py")
    assert receipt["direct_local_import_sha256"] == {
        "AspisV8R19.Q22SamplerInvariants":
            "a4663c405ca28515bd8d7e370d2146017b067286845329273e77bd088c0fa24b"
    }
    assert sha(source) == receipt["source_sha256"]
    assert receipt["source_sha256"] == sha(TARGET) if green else True
    assert receipt["resources"] == {
        "MemoryHigh": "5G", "MemoryMax": "7G", "MemorySwapMax": 0,
        "TasksMax": 128, "lean_flags": "-j1 -M4500"
    }
    assert receipt["measurement_boundary"] == "GNU time Lean-child RSS; wrapper MemoryPeak is not aggregate Lean RSS."
    m = re.search(r"Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([^\n]+)", log)
    rss = re.search(r"Maximum resident set size \(kbytes\): (\d+)", log)
    status = re.search(r"Exit status: (\d+)", log)
    swaps = re.search(r"Swaps: (\d+)", log)
    assert m and rss and status and swaps
    assert receipt["wall_time"] == m.group(1)
    assert receipt["peak_rss_kib"] == int(rss.group(1))
    assert receipt["exit_status"] == int(status.group(1))
    assert receipt["swaps"] == int(swaps.group(1)) == 0
    reports = axioms_from_log(log)
    assert [name for name, _ in reports] == EXPECTED_NAMES
    recorded = receipt["complete_print_axioms"]
    receipt_reports = []
    for line in recorded:
        match = re.search(r"'([^']+)' depends on axioms: \[([\s\S]*?)\]", line)
        assert match, line
        receipt_axioms = [x.strip() for x in match.group(2).replace("\n", " ").split(",") if x.strip()]
        receipt_reports.append((match.group(1), receipt_axioms))
    assert reports == receipt_reports
    assert len(recorded) == len(reports)
    saw_sorry = False
    for report, line in zip(reports, recorded):
        name, axioms = report
        assert line.startswith(f"'{name}' depends on axioms:")
        assert all(ax in ALLOWED or ax == "sorryAx" for ax in axioms)
        if green:
            assert set(axioms) <= ALLOWED and "sorryAx" not in axioms
        else:
            saw_sorry = saw_sorry or "sorryAx" in axioms
    if not green:
        assert saw_sorry
    assert (receipt["exit_status"] == 0) is green


def main() -> None:
    manifest = json.loads((ROOT / "SHA256SUMS.json").read_text())
    expected = set(manifest["files"])
    actual = {p.relative_to(ROOT).as_posix() for p in ROOT.rglob("*")
              if p.is_file() and p.name != "SHA256SUMS.json"}
    assert actual == expected, f"inventory mismatch: missing={expected-actual}, extra={actual-expected}"
    for rel, digest in manifest["files"].items():
        assert sha(ROOT / rel) == digest, rel
    assert sha(TARGET) == sha(ROOT / "source/AspisV8R19/R412LegalQueryEnumeration.lean")
    green_src, _, _ = run_files(GREEN)
    assert sha(TARGET) == sha(green_src)
    assert sha(ROOT / "source/AspisV8R19/Q22SamplerInvariants.lean") == \
        "a4663c405ca28515bd8d7e370d2146017b067286845329273e77bd088c0fa24b"
    assert sha(ROOT / "source/AspisV8R19/Q22SamplerProgram.lean") == \
        "6da9a34123171374f509335778601833aaae2f065ef6e128d79719134b729188"
    assert "R412" in NOTE.read_text()
    assert sha(NOTE) == manifest["external_files"]["../../R412_CURRENT_LEGAL_QUERY_ENUMERATION.md"]
    cache = json.loads((ROOT / "cache-identities.json").read_text())
    assert "not recorded" in cache["measurement"]
    assert "not authenticated" in cache["limitation"]
    check_run(GREEN, green=True)
    for run_id in FAILED:
        check_run(run_id, green=False)
    assert "uncompiled." in TARGET.read_text()
    assert "successful run recorded here supersedes" in NOTE.read_text()
    print("R412 evidence verification: PASS")

if __name__ == "__main__":
    main()
