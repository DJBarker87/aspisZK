#!/usr/bin/env python3
"""Portable read-only verifier for the published R419 evidence bundle."""
from __future__ import annotations
import hashlib, json, pathlib, re
import subprocess, sys

HERE = pathlib.Path(__file__).resolve().parent
EVIDENCE = HERE / "evidence/r419-current-try-fold-normalization-diagnostic"

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def need(ok, msg):
    if not ok: raise AssertionError(msg)

def main():
    inv = json.loads((EVIDENCE / "bundle-inventory.json").read_text())
    listed = {x["path"].removeprefix("evidence/"): x for x in inv["files"]}
    actual = {p.relative_to(EVIDENCE).as_posix(): p for p in EVIDENCE.rglob("*")
              if p.is_file() and p not in {EVIDENCE / "bundle-inventory.json", EVIDENCE / "SHA256SUMS"}}
    need(set(listed) == set(actual), "bundle inventory/file set mismatch")
    for rel, record in listed.items():
        p = EVIDENCE / rel
        need(p.stat().st_size == record["bytes"] and sha(p) == record["sha256"], f"inventory mismatch: {rel}")
    for line in (EVIDENCE / "SHA256SUMS").read_text().splitlines():
        digest, rel = line.split("  ", 1)
        p = EVIDENCE / rel
        need(p.is_file() and sha(p) == digest, f"SHA256SUMS mismatch: {rel}")
    need(not any("__pycache__" in p.parts for p in EVIDENCE.rglob("*")), "unexpected __pycache__")

    cmp = json.loads((EVIDENCE / "r419-expected-tree-audit/expected-candidate-comparison.json").read_text())
    need(cmp["expected_equals_candidate"] and cmp["remaining_diff_count"] == 0, "expected-tree comparison is not zero-diff")
    for path, digest in cmp["evidence_sha256"].items():
        if path.endswith("candidate.llbc"):
            rel = "r419-native-runs/aspis-r419-candidate-1790967913444473000/candidate.llbc"
        else:
            rel = "r419-expected-tree-audit/" + path.removeprefix(".r21-scratch/r419-try-fold-equality-elimination/audit/")
        p = EVIDENCE / rel
        need(p.is_file() and sha(p) == digest, f"comparison input mismatch: {path}")

    candidate = EVIDENCE / "r419-native-runs/aspis-r419-candidate-1790967913444473000"
    need(sha(candidate / "candidate.llbc") == inv["candidate_llbc_sha256"], "candidate hash mismatch")
    result_dir = EVIDENCE / "r419-translation/output/3f22e765d32b-20261002T193059Z"
    result = json.loads((result_dir / "result.json").read_text())
    metrics = json.loads((result_dir / "metrics-receipt.json").read_text())
    command = json.loads((result_dir / "translate-command.json").read_text())
    log = (result_dir / "translate.log").read_text(errors="replace")
    mtime = re.search(r"Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): (\S+)", log)
    mrss = re.search(r"Maximum resident set size \(kbytes\): (\d+)", log)
    mswap = re.search(r"Swaps: (\d+)", log)
    mexit = re.search(r"Exit status: (\d+)", log)
    need(result["translator_exit_status"] == metrics["exit_status"] == 2, "translation exit mismatch")
    need(metrics["wall_time"] == inv["translation"]["wall_time"] and mtime and mtime.group(1) == metrics["wall_time"], "translation wall mismatch")
    need(metrics["peak_rss_kib"] == inv["translation"]["peak_rss_kib"] and mrss and int(mrss.group(1)) == metrics["peak_rss_kib"], "translation RSS mismatch")
    need(metrics["swaps"] == 0 and mswap and int(mswap.group(1)) == 0, "translation swap mismatch")
    need(mexit and int(mexit.group(1)) == 2, "translation raw exit mismatch")
    need(command["candidate_sha256"] == inv["candidate_llbc_sha256"], "translation input mismatch")
    need(command["binary_sha256"] == inv["translation"]["translator_binary_sha256"], "translator binary mismatch")
    need(not result["translation_result"]["generated_dir_exists"] and not result["translation_result"]["translation_json_exists"], "unexpected generated Lean output")
    need("RegionsHierarchy.ml, line 176" in log and "2897:8-2897:35" in log, "translation failure frontier mismatch")
    subprocess.run([sys.executable, str(EVIDENCE / "r419-saved-run-audit/portable_audit.py")], check=True)
    print(f"PASS: {len(listed)} R419 evidence files, original-derived comparison, candidate, and failed translation metrics")

if __name__ == "__main__": main()
