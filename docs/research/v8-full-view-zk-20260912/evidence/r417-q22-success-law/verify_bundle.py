#!/usr/bin/env python3
"""Portable integrity, resource-receipt, and axiom audit for R417."""
from __future__ import annotations
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent
NOTE = ROOT.parents[1] / "R417_CURRENT_Q22_SUCCESS_LAW.md"
TARGET = ROOT.parents[1] / "lean/AspisV8R19/R417Q22SuccessLaw.lean"
GREEN = "1790964475092742000"
FAILED = "1790964434421114000"
EXPECTED_NAMES = [
    "AspisV8R19.R417Q22SuccessLaw.mean_sum",
    "AspisV8R19.R417Q22SuccessLaw.mean_scale",
    "AspisV8R19.R417Q22SuccessLaw.kernel_sum",
    "AspisV8R19.R417Q22SuccessLaw.kernel_scale",
    "AspisV8R19.R417Q22SuccessLaw.kernel_congr_valid",
    "AspisV8R19.R417Q22SuccessLaw.kernel_expansion",
    "AspisV8R19.R417Q22SuccessLaw.success_mass_atom",
    "AspisV8R19.R417Q22SuccessLaw.uniform_success",
]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}

def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()

def run_files(run_id: str) -> tuple[Path, Path, Path]:
    d = ROOT / "runs" / run_id
    return d / "source.lean", d / "lean.log", d / "receipt.json"

def axioms_from_text(text: str) -> list[tuple[str, list[str]]]:
    pattern = re.compile(r"'([^']+)' depends on axioms: \[([\s\S]*?)\]")
    out = []
    for name, body in pattern.findall(text):
        axioms = [x.strip() for x in body.replace("\n", " ").split(",") if x.strip()]
        out.append((name, axioms))
    return out

def check_run(run_id: str, *, green: bool) -> None:
    source, log_path, receipt_path = run_files(run_id)
    receipt = json.loads(receipt_path.read_text())
    log = log_path.read_text(errors="replace")
    assert receipt["target"] == "AspisV8R19/R417Q22SuccessLaw.lean"
    assert receipt["source_revision"] == "c145fb14be60e3b2553713927228ac62876dbab2"
    assert receipt["runner_sha256"] == sha(ROOT / "run_focus.py")
    assert sha(source) == receipt["source_sha256"]
    expected_imports = {
        "AspisV8R19.R411EqualLegalQueryMass":
            "b209c043003f7d2b8d778f59693daf93c2c705201094a292765a9e8a372ec362"
    }
    if green:
        expected_imports["AspisV8R19.R412LegalQueryEnumeration"] = \
            "2a950c0cbb915c496a8ba0ad4738f35d73d1381693b07183e08d57f6a1855a36"
        assert receipt["source_sha256"] == sha(TARGET)
    assert receipt["direct_local_import_sha256"] == expected_imports
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
    reports = axioms_from_text(log)
    receipt_reports = axioms_from_text("\n".join(receipt["complete_print_axioms"]))
    assert reports == receipt_reports
    assert [name for name, _ in reports] == EXPECTED_NAMES
    if green:
        assert all(set(axioms) <= ALLOWED and "sorryAx" not in axioms for _, axioms in reports)
        assert receipt["exit_status"] == 0
    else:
        assert any("sorryAx" in axioms for _, axioms in reports)
        assert receipt["exit_status"] == 1

def main() -> None:
    manifest = json.loads((ROOT / "SHA256SUMS.json").read_text())
    expected = set(manifest["files"])
    actual = {p.relative_to(ROOT).as_posix() for p in ROOT.rglob("*")
              if p.is_file() and p.name != "SHA256SUMS.json"}
    assert actual == expected, f"inventory mismatch: missing={expected-actual}, extra={actual-expected}"
    for rel, digest in manifest["files"].items():
        assert sha(ROOT / rel) == digest, rel
    assert sha(TARGET) == sha(ROOT / "source/AspisV8R19/R417Q22SuccessLaw.lean")
    assert sha(TARGET) == sha(run_files(GREEN)[0])
    assert sha(ROOT / "source/AspisV8R19/R411EqualLegalQueryMass.lean") == \
        "b209c043003f7d2b8d778f59693daf93c2c705201094a292765a9e8a372ec362"
    assert sha(ROOT / "source/AspisV8R19/R412LegalQueryEnumeration.lean") == \
        "2a950c0cbb915c496a8ba0ad4738f35d73d1381693b07183e08d57f6a1855a36"
    assert sha(NOTE) == manifest["external_files"]["../../R417_CURRENT_Q22_SUCCESS_LAW.md"]
    cache = json.loads((ROOT / "cache-identities.json").read_text())
    assert "not recorded" in cache["measurement"] and "not authenticated" in cache["limitation"]
    check_run(GREEN, green=True)
    check_run(FAILED, green=False)
    print("R417 evidence verification: PASS")

if __name__ == "__main__":
    main()
