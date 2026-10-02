#!/usr/bin/env python3
"""Read-only portable audit of the R419 evidence bundle's saved run records."""
from __future__ import annotations

import hashlib
import json
import pathlib
import re

HERE = pathlib.Path(__file__).resolve().parent
EVIDENCE = HERE.parent
RUNS = EVIDENCE / "r419-native-runs"
R396 = EVIDENCE / "provenance/r396-private-batch-unmonomorphized-plan/R396PrivateBatchUnmonomorphized.llbc"
R396_SHA = "399020435e94aaa7135c06d68445e9b936bd22fe6d1e1d197ee708d448d584ae"
REV = "3f22e765d32b16d016f4ff603d599ea72838c37a"
CAPS = {"MemoryHigh": "5G", "MemoryMax": "7G", "MemorySwapMax": 0, "TasksMax": 128}


def sha(p: pathlib.Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()


def need(ok: bool, msg: str) -> None:
    if not ok:
        raise AssertionError(msg)


def integer(log: str, label: str) -> int | None:
    m = re.search(rf"^\s*{re.escape(label)}: (\d+)\s*$", log, re.M)
    return int(m.group(1)) if m else None


def exit_status(log: str) -> int | None:
    status = integer(log, "Exit status")
    if status is not None:
        return status
    m = re.search(r"Main processes terminated with: code=exited/status=(\d+)", log)
    return int(m.group(1)) if m else None


def main() -> None:
    need(R396.is_file() and sha(R396) == R396_SHA, "bundled immutable R396 input hash mismatch")
    run_dirs = sorted(p for p in RUNS.iterdir() if p.is_dir())
    need(len(run_dirs) == 13, f"expected 13 saved R419 run folders, found {len(run_dirs)}")
    nonzero = []

    for d in run_dirs:
        rp, lp = d / "receipt.json", d / "raw.log"
        need(rp.is_file() and lp.is_file(), f"missing receipt/log: {d.name}")
        rec = json.loads(rp.read_text())
        log = lp.read_text(errors="replace")
        need(rec.get("source_revision") == REV, f"revision mismatch: {d.name}")
        need(rec.get("resources") == CAPS, f"resource scope mismatch: {d.name}")
        need(rec.get("exit_status") == exit_status(log), f"exit status mismatch: {d.name}")
        mt = re.search(r"Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): (\S+)", log)
        need(mt and mt.group(1) == rec.get("wall_time"), f"wall time mismatch: {d.name}")
        need(integer(log, "Maximum resident set size (kbytes)") == rec.get("peak_rss_kib"), f"RSS mismatch: {d.name}")
        need(integer(log, "Swaps") == rec.get("swaps") == 0, f"swap mismatch: {d.name}")

        source_hashes = rec.get("source_sha256", {})
        missing_snapshots = []
        for name, digest in source_hashes.items():
            saved = d / name
            if saved.is_file():
                need(sha(saved) == digest, f"saved source snapshot mismatch: {d.name}/{name}")
            else:
                missing_snapshots.append(name)
        if rec.get("action", "").startswith("compile-"):
            need(not missing_snapshots, f"compile source snapshot missing: {d.name}: {missing_snapshots}")

        if rec.get("action") == "test" or d.name.startswith("aspis-r419-candidate-"):
            link = pathlib.Path(rec["compiler_receipt"]).parent.name
            build_receipt = RUNS / link / "receipt.json"
            need(build_receipt.is_file(), f"linked compiler receipt absent: {d.name}")
            need(sha(build_receipt) == rec.get("compiler_receipt_sha256"), f"linked compiler receipt hash mismatch: {d.name}")
            br = json.loads(build_receipt.read_text())
            need(br.get("source_sha256") == source_hashes, f"linked source hash map mismatch: {d.name}")

        if d.name.startswith("aspis-r419-candidate-"):
            need(rec.get("input_sha256") == R396_SHA, f"candidate input identity mismatch: {d.name}")
            result = json.loads((d / "result.json").read_text())
            need(result == rec.get("native_result"), f"candidate result mismatch: {d.name}")
            need(result.get("original_post_sha256") == R396_SHA, f"candidate modified original input: {d.name}")
            output = d / "candidate.llbc"
            if rec["exit_status"] == 0:
                need(output.is_file() and sha(output) == result.get("output_sha256"), f"candidate output hash mismatch: {d.name}")
            else:
                need(not output.exists(), f"failed candidate wrote output: {d.name}")

        if rec.get("exit_status") != 0:
            nonzero.append({"run": d.name, "exit_status": rec["exit_status"]})

    need(
        {(x["run"], x["exit_status"]) for x in nonzero} == {
            ("aspis-r419-candidate-1790967775715172000", 101),
            ("aspis-r419-compile-test-1790967044819648000", 1),
        }
        and len(nonzero) == 2,
        "nonzero historical run/status pairs mismatch",
    )
    print("PASS: 13 saved R419 runs; source/candidate/compiler links, statuses, wall/RSS/swap, caps, and R396 identity verified")
    print("Nonzero attempts retained:", json.dumps(nonzero, sort_keys=True))


if __name__ == "__main__":
    main()
