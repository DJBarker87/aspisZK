#!/usr/bin/env python3
"""Verify the retained R18 measurement bundle without running a replay."""
import hashlib
import json
from pathlib import Path
import subprocess
import tarfile

root = Path(__file__).resolve().parent
archive = root / "evidence.tar.gz"
sha = lambda value: hashlib.sha256(value).hexdigest()
assert sha(archive.read_bytes()) == "3ad3b3096647b2bfa4b90dbba5257ad7d20e420f5d7d68b14e7833db4b88dd6f"
with tarfile.open(archive) as tar:
    members = tar.getmembers()
    assert len(members) == len({m.name for m in members}) == 73
    assert all(m.isfile() and not m.name.endswith(".key") for m in members)
    data = {m.name: tar.extractfile(m).read() for m in members}
manifest = json.loads(data["BUNDLE-MANIFEST.json"])
assert set(manifest) == set(data) - {"BUNDLE-MANIFEST.json"}
for name, digest in manifest.items():
    assert sha(data[name]) == digest, name
summary = json.loads(data["SUMMARY.json"])
assert summary == json.loads((root / "SUMMARY.json").read_text())
repo = Path(subprocess.check_output(["git", "rev-parse", "--show-toplevel"], text=True).strip())
sources = {}
for label in ["before", "after"]:
    pins = json.loads(data[label + "-manifest.json"])
    reconstructed = subprocess.check_output(["git", "archive", pins["revision"], "--", *pins["files"]], cwd=repo)
    assert sha(reconstructed) == pins["archive_sha256"], label
    sources[label] = pins
assert set(sources["before"]["files"]) == set(sources["after"]["files"])
assert {p for p, h in sources["before"]["files"].items() if sources["after"]["files"][p] != h} == {
    "crates/aspis-r1-cost-probe/src/r1_wire.rs", "crates/aspis-r1-cost-probe/src/sampler.rs"}
for label, target in summary["targets"].items():
    receipt = json.loads(data[f"runs/{label}/receipt.json"])
    assert receipt["exit"] == target["exit"] == 0
    assert receipt["swap_current_bytes"] == target["swaps"] == 0
    assert receipt["limits"] == {"memory.high": "8589934592", "memory.max": "10737418240", "memory.swap.max": "0"}
    assert all(int(line.split()[1]) == 0 for line in receipt["events_after"].splitlines())
assert not summary["targets"]["after-sbf"]["accepted"]
assert b"1 passed; 0 failed" in data["runs/after-counter/build.log"]
assert b"measured_core_call_counts_include_zero_progress_checkpoint ... ok" in data["runs/after-counter/build.log"]
comparison = json.loads(data["cu-comparison-1/comparison.json"])
assert comparison == summary["comparison"]
assert comparison["delta"] == {"stage1": 88, "stage2": 0, "sum": 88}
assert all(comparison[k] for k in ["both_admitted_pairs_accepted", "checkpoint_equal", "asr8_equal", "initial_images_equal"])
assert not comparison["setup_cu_included"]
for name in ["checkpoint.bin", "stage2.return.bin", "initial-accounts.json"]:
    assert data["cu-comparison-1/before/" + name] == data["cu-comparison-1/after/" + name]
for side in ["before", "after"]:
    for stage in ["stage1", "stage2"]:
        result = json.loads(data[f"cu-comparison-1/{side}/{stage}.json"])
        assert result["error"] is None
        assert result["compute_units"] == comparison[side][stage]
print("PASS: 72 bundle hashes; 503-file source snapshots; two-source-only delta; counter and admitted-route CU receipts. No formal refinement claim.")
