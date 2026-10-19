#!/usr/bin/env python3
"""Check source/output evidence without repeating a build or replay."""
from pathlib import Path
import hashlib
import io
import json
import subprocess
import tarfile

b = Path(__file__).resolve().parent
repo = b.parents[4]
sha = lambda data: hashlib.sha256(data).hexdigest()
assert sha((b / "evidence.tar.gz").read_bytes()) == "5f7c2d96a5187136f2e7269003dce093b7bc48a36278a60ee0a2138fa792d661"
with tarfile.open(b / "evidence.tar.gz") as t:
    entries = t.getmembers()
    assert len(entries) == len({m.name for m in entries}) == 68
    assert all(m.isfile() and not m.name.endswith(".key") and "keypair" not in m.name for m in entries)
    data = {m.name: t.extractfile(m).read() for m in entries}
manifest = json.loads(data["BUNDLE-MANIFEST.json"])
assert set(manifest) == set(data) - {"BUNDLE-MANIFEST.json"}
for name, digest in manifest.items():
    assert sha(data[name]) == digest, name
summary = json.loads(data["SUMMARY.json"])
assert summary == json.loads((b / "SUMMARY.json").read_text())
sources = {side: json.loads(data[side + "-manifest.json"]) for side in ["before", "after"]}
queries = {f"{p['revision']}:{name}": digest for p in sources.values() for name, digest in p['files'].items()}
stream = io.BytesIO(subprocess.check_output(["git", "cat-file", "--batch"], cwd=repo, input=("\n".join(queries) + "\n").encode()))
for query, digest in queries.items():
    header = stream.readline().decode().split()
    assert len(header) == 3 and header[1] == "blob", query
    assert sha(stream.read(int(header[2]))) == digest, query
    assert stream.read(1) == b"\n"
assert stream.read() == b""
before, after = sources["before"]["files"], sources["after"]["files"]
assert set(after) - set(before) == {"crates/aspis-statement/examples/j1_terminal_codec_trace.rs"}
assert not set(before) - set(after)
assert {name for name in before if before[name] != after[name]} == {
    "crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs",
    "crates/aspis-statement/src/pool_v1/pair_tree_profile.rs",
    "crates/aspis-statement/src/pool_v1/pair_terminal.rs"}
for label, target in summary["targets"].items():
    r = json.loads(data[f"runs/{label}/receipt.json"])
    assert r["exit"] == target["exit"] == 0
    assert r["swap_current_bytes"] == target["swaps"] == 0
    assert r["limits"] == {"memory.high": "8589934592", "memory.max": "10737418240", "memory.swap.max": "0"}
    assert all(int(line.split()[1]) == 0 for line in r["events_after"].splitlines())
    assert sha(data[f"runs/{label}/runner.py"]) == r["runner_sha256"]
    assert r["source_manifest_sha256"] == sha(data[("before" if label == "before-sbf" else "after") + "-manifest.json"])
assert summary["targets"]["before-sbf"]["reused"]
assert b"measured_core_call_counts_include_zero_progress_checkpoint ... ok" in data["runs/after-counter/build.log"]
c = json.loads(data["cu-comparison-1/comparison.json"])
assert c == summary["comparison"]
assert c["delta"] == {"stage1": 563, "stage2": 366, "sum": 929}
assert all(c[k] for k in ["both_admitted_pairs_accepted", "checkpoint_equal", "asr8_equal", "initial_images_equal"])
assert not c["setup_cu_included"]
for name in ["checkpoint.bin", "stage2.return.bin", "initial-accounts.json"]:
    assert data[f"cu-comparison-1/before/{name}"] == data[f"cu-comparison-1/after/{name}"]
for side in ["before", "after"]:
    for stage in ["stage1", "stage2"]:
        r = json.loads(data[f"cu-comparison-1/{side}/{stage}.json"])
        assert r["error"] is None and r["compute_units"] == c[side][stage]
print("PASS: 67 member hashes, 1007 Git source pins, four capped receipts, exact three production-source changes, counter and CU pair; no universal QV claim")
