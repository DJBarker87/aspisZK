#!/usr/bin/env python3
"""Check pinned source/candidate/result hashes and bounded-run receipt."""

import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


manifest = json.loads((ROOT / "manifest.json").read_text())
for key in ("transform", "unit_tests", "candidate_llbc"):
    entry = manifest[key]
    assert digest(ROOT / entry["path"]) == entry["sha256"], key
unit_output = manifest["unit_test_output"]
assert digest(ROOT / unit_output["path"]) == unit_output["sha256"]
input_path = Path(__file__).resolve().parents[2] / (
    "docs/research/100bit-spend-path-20261013/lean-candidates/"
    "s4-stdlib-fromfn-isolation-v1-20261021/remote-attempts/attempt-v2/from_fn.llbc"
)
assert digest(input_path) == manifest["input_llbc"]["sha256"]

result_dir = ROOT / "results/bounded-aeneas-v1"
receipt = json.loads((result_dir / "receipt.json").read_text())
admission = json.loads((result_dir / "admission.json").read_text())
assert receipt["exit_status"] == manifest["aeneas_run"]["exit_status"] == 2
assert receipt["input_sha256"] == manifest["candidate_llbc"]["sha256"]
assert receipt["candidate_binary_sha256"] == manifest["tool"]["existing_candidate_binary_sha256"]
assert receipt["scope_swap_max_bytes"] == 0
assert receipt["swap_events_reported_by_time"] == 0
assert admission["registration"]["limits"] == {
    "memory.high": str(manifest["aeneas_run"]["memory_high_bytes"]),
    "memory.max": str(manifest["aeneas_run"]["memory_max_bytes"]),
    "memory.swap.max": "0",
}
assert not any((result_dir / "generated").rglob("*.lean")) if (result_dir / "generated").exists() else True
print("PASS: candidate pins, bounded-run receipt and no-generated-Lean status")
