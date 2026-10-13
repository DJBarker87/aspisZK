#!/usr/bin/env python3
"""Validate curated focused Lean receipt/source links; not a release audit."""

from __future__ import annotations

import hashlib
import json
import subprocess
import sys
from pathlib import Path


HERE = Path(__file__).resolve().parent
REPO = HERE.parents[4]
LEAN_DIR = REPO / "docs/research/100bit-spend-path-20261013/lean"
BASE_REVISION = "2df5bf1a6f296a09cff71a886185112b66f0235a"

# Explicitly selected green targets. Failed attempts remain inventoried below.
SOURCES = {
    "R1ConcreteProjection": "ConcreteProjection.lean",
    "R1TwoFoldExtraction": "TwoFoldExtraction.lean",
    "R1ConcreteBinding": "ConcreteBinding.lean",
    "R1SecondFoldMatched": "SecondFoldMatched.lean",
    "R1FoldCoefficientBridge": "FoldCoefficientBridge.lean",
    "R1FunctionalWeights": "FunctionalWeights.lean",
    "R1FirstFold": "FirstFold.lean",
    "R1JointList": "JointList.lean",
    "R1InitialResponses": "InitialResponses.lean",
}
GREEN = {
    "R1ConcreteProjection": "c",
    "R1TwoFoldExtraction": "f",
    "R1ConcreteBinding": "c",
    "R1SecondFoldMatched": "b",
    "R1FoldCoefficientBridge": "b",
    "R1FunctionalWeights": "b",
    "R1FirstFold": "a",
    "R1JointList": "c",
    "R1InitialResponses": "b",
}
ATTEMPT_PREFIXES = tuple(SOURCES)
RUNNER_FILES = (
    "compile-one.sh",
    "run2.py",
    "environment-base.json",
    "import-only-review.json",
)


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def fail(message: str) -> None:
    print(f"ERROR: {message}", file=sys.stderr)
    raise SystemExit(1)


def main() -> None:
    base = subprocess.run(
        ["git", "-C", str(REPO), "rev-parse", BASE_REVISION],
        check=True,
        capture_output=True,
        text=True,
    ).stdout.strip()

    source_records = {}
    for module, filename in SOURCES.items():
        path = LEAN_DIR / filename
        if not path.is_file():
            fail(f"missing Lean source: {path}")
        source_records[module] = {
            "lean_file": str(path.relative_to(REPO)),
            "sha256": sha256(path),
        }

    selected_records = {}
    for module, attempt in GREEN.items():
        stem = f"{module}-{attempt}"
        receipt_path = HERE / f"{stem}.receipt.json"
        sidecar_path = HERE / f"{stem}.sha256"
        output_path = HERE / f"{stem}.out.log"
        time_path = HERE / f"{stem}.time.log"
        for path in (receipt_path, sidecar_path, output_path, time_path):
            if not path.is_file():
                fail(f"missing selected artifact: {path.name}")
        receipt = json.loads(receipt_path.read_text())
        receipt_hash = receipt.get("source_sha256")
        sidecar_hash = sidecar_path.read_text().strip().split()[0]
        current_hash = source_records[module]["sha256"]
        if receipt.get("target") != module or receipt.get("attempt") != attempt:
            fail(f"receipt identity mismatch: {stem}")
        if receipt.get("exit_status") != 0:
            fail(f"selected receipt is not green: {stem}")
        if receipt_hash != current_hash or sidecar_hash != current_hash:
            fail(
                f"selected source hash mismatch for {stem}: "
                f"receipt={receipt_hash}, sidecar={sidecar_hash}, current={current_hash}"
            )
        output = output_path.read_text(errors="replace")
        if "sorryAx" in output:
            fail(f"selected green output contains sorryAx: {stem}")
        selected_records[module] = {
            "attempt": attempt,
            "receipt": receipt_path.name,
            "output": output_path.name,
            "time_log": time_path.name,
            "source_sha256": current_hash,
            "exit_status": 0,
            "sorryAx_found": False,
            "elapsed_wall_clock": receipt.get("elapsed_wall_clock"),
            "max_rss_kib": receipt.get("max_rss_kib"),
            "swaps": receipt.get("swaps"),
            "cgroup": receipt.get("cgroup"),
            "lean_threshold_mb": receipt.get("lean_threshold_mb"),
        }

    attempts = []
    for receipt_path in sorted(HERE.glob("R1*.receipt.json")):
        receipt = json.loads(receipt_path.read_text())
        module = receipt.get("target")
        if module not in SOURCES:
            continue
        attempt = receipt.get("attempt")
        stem = f"{module}-{attempt}"
        record = {
            "target": module,
            "attempt": attempt,
            "receipt": receipt_path.name,
            "receipt_sha256": sha256(receipt_path),
            "source_sha256": receipt.get("source_sha256"),
            "exit_status": receipt.get("exit_status"),
            "selected_green": GREEN[module] == attempt,
        }
        for suffix, key in (("out.log", "output"), ("time.log", "time_log"), ("sha256", "source_sidecar")):
            candidate = HERE / f"{stem}.{suffix}"
            if candidate.is_file():
                record[key] = candidate.name
                record[f"{key}_sha256"] = sha256(candidate)
        attempts.append(record)

    runner_context = {}
    for filename in RUNNER_FILES:
        path = HERE / filename
        if path.is_file():
            runner_context[filename] = {"sha256": sha256(path), "bytes": path.stat().st_size}

    result = {
        "purpose": "focused Lean receipt/source provenance validation only",
        "limitations": [
            "not a full release or reproducibility audit",
            "does not audit the complete Lean cache or imported object provenance",
            "restoration, final-response, geometry and import-rebuild receipts are in separate adjacent evidence folders",
        ],
        "base_git_revision": base,
        "expected_base_git_revision": BASE_REVISION,
        "base_revision_resolves": base == BASE_REVISION,
        "lean_sources": source_records,
        "selected_green_receipts": selected_records,
        "retained_attempts": attempts,
        "runner_environment_union_cache_context": runner_context,
        "validator": {
            "file": Path(__file__).name,
            "sha256": sha256(Path(__file__)),
        },
    }
    out = HERE / "provenance-validation.json"
    out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(f"validated {len(selected_records)} selected green targets")
    print(f"retained {len(attempts)} receipt attempts")
    print(f"base revision: {base}")
    print(f"wrote {out}")


if __name__ == "__main__":
    main()
