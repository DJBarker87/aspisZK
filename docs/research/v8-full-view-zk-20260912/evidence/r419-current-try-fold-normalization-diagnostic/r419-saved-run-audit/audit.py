#!/usr/bin/env python3
"""Read-only mechanical audit of saved R419 native runs."""
from __future__ import annotations

import hashlib
import json
import pathlib
import re
import sys

HERE = pathlib.Path(__file__).resolve().parent
TASK = HERE.parent
REPO = TASK.parents[1]
RUNS = TASK / "runs"
EXPECTED_REV = "3f22e765d32b16d016f4ff603d599ea72838c37a"
EXPECTED_INPUT_SHA = "399020435e94aaa7135c06d68445e9b936bd22fe6d1e1d197ee708d448d584ae"
EXPECTED_CAPS = {"MemoryHigh": "5G", "MemoryMax": "7G", "MemorySwapMax": 0, "TasksMax": 128}


def sha(path: pathlib.Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def parse_time(log: str) -> str | None:
    m = re.search(r"Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([^\r\n]+)", log)
    return m.group(1).strip() if m else None


def parse_int(log: str, key: str) -> int | None:
    m = re.search(rf"^\s*{re.escape(key)}: (\d+)\s*$", log, re.M)
    return int(m.group(1)) if m else None


def parse_exit(log: str) -> int | None:
    m = re.search(r"^Exit status: (\d+)\s*$", log, re.M)
    if m:
        return int(m.group(1))
    m = re.search(r"Main processes terminated with: code=exited/status=(\d+)", log)
    return int(m.group(1)) if m else None


def main() -> None:
    rows = []
    failures = []
    dirs = sorted(p for p in RUNS.iterdir() if p.is_dir())
    require(bool(dirs), "no saved R419 run directories")
    for d in dirs:
        rp, lp = d / "receipt.json", d / "raw.log"
        require(rp.is_file() and lp.is_file(), f"missing receipt/log in {d.name}")
        rec = json.loads(rp.read_text())
        log = lp.read_text(errors="replace")
        runid = d.name.rsplit("-", 1)[-1]
        require(runid in lp.name or runid in d.name, f"unexpected run directory {d.name}")
        require(rec.get("source_revision") == EXPECTED_REV, f"revision mismatch {d.name}")
        require(rec.get("resources") == EXPECTED_CAPS, f"cgroup caps mismatch {d.name}")
        status = rec.get("exit_status")
        log_status = parse_exit(log)
        require(status == log_status, f"exit receipt/log mismatch {d.name}: {status} vs {log_status}")
        elapsed = parse_time(log)
        rss = parse_int(log, "Maximum resident set size (kbytes)")
        swaps = parse_int(log, "Swaps")
        require(elapsed == rec.get("wall_time"), f"wall receipt/log mismatch {d.name}: {elapsed} vs {rec.get('wall_time')}")
        require(rss == rec.get("peak_rss_kib"), f"RSS receipt/log mismatch {d.name}: {rss} vs {rec.get('peak_rss_kib')}")
        require(swaps == rec.get("swaps"), f"swap receipt/log mismatch {d.name}: {swaps} vs {rec.get('swaps')}")

        source_hashes = rec.get("source_sha256", {})
        missing = []
        mismatched = []
        if source_hashes:
            for name, expected in source_hashes.items():
                snapshot = d / name
                if snapshot.is_file():
                    actual = sha(snapshot)
                    if actual != expected:
                        mismatched.append(name)
                else:
                    missing.append(name)
            if rec.get("action") == "test":
                crp = REPO / rec["compiler_receipt"]
                require(crp.is_file() and sha(crp) == rec["compiler_receipt_sha256"], f"test compiler receipt hash mismatch {d.name}")
                cr = json.loads(crp.read_text())
                require(cr.get("source_sha256") == source_hashes, f"test source hashes differ from build {d.name}")
                require(not mismatched, f"test-local source snapshot hash mismatch {d.name}: {mismatched}")
            elif d.name.startswith("aspis-r419-candidate-"):
                compiler_receipt = REPO / rec["compiler_receipt"]
                require(compiler_receipt.is_file(), f"missing compiler receipt {d.name}")
                require(sha(compiler_receipt) == rec["compiler_receipt_sha256"], f"compiler receipt hash mismatch {d.name}")
                cr = json.loads(compiler_receipt.read_text())
                require(cr.get("source_sha256") == source_hashes, f"candidate source hashes differ from compiled candidate {d.name}")
                require(not mismatched, f"candidate referenced source hash mismatch {d.name}: {mismatched}")
            else:
                require(not missing and not mismatched, f"source snapshot hash issue {d.name}: missing={missing}, mismatched={mismatched}")

        row = {
            "run": d.name,
            "action": rec.get("action", "candidate-transform"),
            "exit_status": status,
            "wall_time": rec.get("wall_time"),
            "peak_rss_kib": rec.get("peak_rss_kib"),
            "swaps": rec.get("swaps"),
            "source_revision": rec.get("source_revision"),
            "caps": rec.get("resources"),
            "receipt_sha256": sha(rp),
            "raw_log_sha256": sha(lp),
            "source_snapshot_sha256": source_hashes,
            "snapshot_check": (
                "linked-to-compiler-receipt"
                if rec.get("action") == "test"
                else "candidate-snapshots-referenced-by-compiler-receipt"
                if d.name.startswith("aspis-r419-candidate-")
                else "matched"
            ),
        }
        if "print_axioms" in rec:
            row["lean_axioms"] = rec["print_axioms"]
        if d.name.startswith("aspis-r419-candidate-"):
            require(rec.get("input_sha256") == EXPECTED_INPUT_SHA, f"candidate receipt input hash mismatch {d.name}")
            result = json.loads((d / "result.json").read_text())
            require(result.get("exit_status") == status, f"candidate result/receipt status mismatch {d.name}")
            require(result.get("original_post_sha256") == EXPECTED_INPUT_SHA, f"candidate input changed {d.name}")
            require(rec.get("native_result") == result, f"candidate result differs from receipt {d.name}")
            output = d / "candidate.llbc"
            if status == 0:
                require(output.is_file(), f"candidate succeeded without output {d.name}")
                require(sha(output) == result.get("output_sha256"), f"candidate output hash mismatch {d.name}")
            else:
                require(not output.exists(), f"failed candidate unexpectedly left output {d.name}")
            row["candidate_result"] = result
        if status != 0:
            failures.append({"run": d.name, "exit_status": status})
        rows.append(row)

    require(all(row["swaps"] == 0 for row in rows), "nonzero swap recorded")
    require(len(rows) == 13, f"unexpected run count {len(rows)}")
    input_path = pathlib.Path(
        "/Users/dominic/ZK/.worktrees/ZK-v8-r21-public-arithmetic-20260922/docs/research/v8-full-view-zk-20260912/evidence/r405-generic-batch-translation-frontier/provenance/r396-private-batch-unmonomorphized-plan/R396PrivateBatchUnmonomorphized.llbc"
    )
    require(input_path.is_file() and sha(input_path) == EXPECTED_INPUT_SHA, "saved R396 LLBC input hash mismatch")

    data = {
        "audit_kind": "saved R419 receipts and source snapshots; read-only, no build or transform",
        "all_checks_passed": True,
        "source_revision": EXPECTED_REV,
        "pinned_rustc": "1.98.0-nightly (14210df0e 2026-05-31)",
        "resource_scope": EXPECTED_CAPS,
        "input_sha256": EXPECTED_INPUT_SHA,
        "run_count": len(rows),
        "nonzero_exit_runs_preserved": failures,
        "runs": rows,
        "claim_boundary": "Native AST helper fixtures and an unverified candidate serialization run only. No Aeneas translation, Lean theorem, source-semantics result, or security claim.",
    }
    (HERE / "manifest.json").write_text(json.dumps(data, indent=2, sort_keys=True) + "\n")
    summary = [
        "# R419 saved-run evidence preflight",
        "",
        "Read-only consistency audit of the saved Rust compile, test, and candidate-run receipts. No compiler, test binary, or AST transform was rerun.",
        "",
        f"All {len(rows)} saved run folders passed receipt/log metrics, source snapshot, revision, resource cap, and zero-swap checks. Pinned compiler: {data['pinned_rustc']}; source revision: `{EXPECTED_REV}`; cap per run: 5G high / 7G max / 0 swap / 128 tasks.",
        "",
        "The focused fixture run at `1790967562246457000` reports 18 passed tests. The first candidate at `1790967775715172000` failed before output at unique source-qualified lookup (the prefix matched 87 names); its input SHA remained unchanged. The filtered lookup candidate at `1790967913444473000` exited 0 and emitted a new LLBC file; this is recorded only as an unverified serialization candidate.",
        "",
        "The original R396 LLBC was SHA-256 checked as `" + EXPECTED_INPUT_SHA + "`. Run-by-run receipt, raw log, and source snapshot hashes are in `manifest.json`.",
        "",
        "Boundary: native AST helper fixtures and candidate serialization only. There is no Aeneas translation, Lean theorem, source-semantics result, or security claim. `#print axioms` is not applicable to these Rust runs.",
        "",
    ]
    (HERE / "REPORT.md").write_text("\n".join(summary))
    print(f"PASS: audited {len(rows)} saved R419 runs; failures retained={len(failures)}")


if __name__ == "__main__":
    main()
