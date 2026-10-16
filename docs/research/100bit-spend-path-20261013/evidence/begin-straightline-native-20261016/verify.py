#!/usr/bin/env python3
"""Read/hash-only evidence check; never executes Rust, Lean, SBF or runtime."""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import tarfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
sha = lambda raw: hashlib.sha256(raw).hexdigest()
pin = json.loads((HERE / "archive-pin.json").read_text())
archive = HERE / pin["path"]
assert archive.stat().st_size == pin["bytes"] and sha(archive.read_bytes()) == pin["sha256"]
with tarfile.open(archive) as tf:
    def read(name):
        return tf.extractfile(name).read()

    def j(name):
        return json.loads(read(name))

    summary = j("SUMMARY.json")
    assert summary == json.loads((HERE / "SUMMARY.json").read_text())
    initial, final = j("inputs-initial.json"), j("inputs.json")
    assert len(initial["files"]) == 530 and len(final["files"]) == 532
    for name, digest in final["files"].items():
        raw = read(name)
        assert sha(raw) == digest, name
        actual = subprocess.check_output([
            "git", "-C", str(ROOT), "show",
            final["source_revision"] + ":" + name.removeprefix("source/"),
        ])
        assert raw == actual, name
    assert read("runs/codec1233/stdout.log") == read("baseline/codec1233.stdout.log")
    assert sha(read("runs/codec1233/stdout.log")) == summary["codec_trace_sha256"]
    assert read("runs/codec1233/stdout.log").splitlines()[-1] == b"complete 1233"
    before, after = j("baseline/ordered-counter.json"), j("ordered-counter.json")
    assert before["ordered_digest_calls"] == after["ordered_digest_calls"]
    assert len(after["ordered_digest_calls"]) == 583
    assert before["acceptance"] == after["acceptance"]
    for value in [before, after]:
        value["hash_input_counts"]["repeated_exact_inputs"].sort(key=lambda row: row["input_hex"])
    assert before["hash_input_counts"] == after["hash_input_counts"]
    assert after["hash_input_counts"]["tx1_raw_calls"] == 349
    assert after["hash_input_counts"]["tx2_raw_calls"] == 234
    checkpoint = read("runs/checkpoint23-staged-fixtures/stdout.log").decode()
    actual = re.findall(r"test r1_pool_adapter::checkpoint_tests::(\w+) \.\.\. ok", checkpoint)
    expected = re.findall(r"#\[test\]\s*fn\s+(\w+)", read(
        "source/programs/r1-cost-probe/src/r1_checkpoint_tests.rs").decode())
    assert len(expected) == len(actual) == 23 and set(expected) == set(actual)
    overlay = read("runs/begin-failure-overlay/stdout.log").decode()
    injected = re.findall(r"failure (Lookup|Semantic)\((\d+)\):", overlay)
    assert len(injected) == 20 and set(injected) == {
        (kind, str(row)) for kind in ["Lookup", "Semantic"] for row in range(3, 13)
    }
    assert "test result: ok. 2 passed; 0 failed;" in overlay
    for result in summary["native_results"]:
        assert result["exit_status"] == 0 and result["process_swaps"] == 0
        assert result["limits"] == {
            "memory.high": "6442450944", "memory.max": "8589934592", "memory.swap.max": "0",
        }
        label = result["label"]
        assert result["stdout_sha256"] == sha(read("runs/" + label + "/stdout.log"))
        assert result["stderr_sha256"] == sha(read("runs/" + label + "/stderr.log"))
        if result.get("wrapper_exit_status") == 1:
            runner = "runs/" + label + "/failed-postprocess-runner.py"
            assert result["cgroup_memory_peak_bytes"] is None
        else:
            runner = "run-host.py"
        assert result["runner_sha256"] == sha(read(runner))
        reservation = j(label + "-reservation.json")
        assert reservation["total_with_new_bytes"] < reservation["safe_working_limit_bytes"]
    assert j("runs/checkpoint23/receipt.json")["exit_status"] == 101
    assert summary["no_Lean"] and summary["no_SBF"] and summary["no_runtime_harness"]
print("PASS: 532 Git-exact files; codec1233 bytes, saved-proof583 calls/checkpoint, checkpoint23, 20 injected failures+success; wrapper/staging failures retained")
