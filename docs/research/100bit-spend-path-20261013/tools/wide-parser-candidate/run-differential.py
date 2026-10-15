#!/usr/bin/env python3
"""Run the isolated release-mode WideExact baseline/candidate differential."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

EXPECTED = {
    "baseline.rs": "28df5a1abee13bde4b3aa9eeceb0489bedf00531f298460954a97661f5f1baea",
    "baseline/wide_exact.rs": "56c26ce33cd0caee95f33474bfc351c5409503b6af665dba7c8837d6ec1068ea",
    "field.rs": "28df5a1abee13bde4b3aa9eeceb0489bedf00531f298460954a97661f5f1baea",
    "field/wide_exact.rs": "940e31f8056b6a3b9422d3fa31ae6cbe3c4084d79885bb8fd5b4a14c56dd7d06",
    "differential.rs": "66f69b69f2204c47593058fba5c019d1c0e25c8c9ba69ad14649e8c983250f64",
}
TEST = "wideexact_candidate_matches_baseline_field_module"
EXPECTED_RUSTC_COMMIT = "14210df0e27ccd7d9e6a05b8085cbd438e4bbc65"


def digest(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for block in iter(lambda: f.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def run_timed(label, command, kit, env):
    time_log = kit / "results" / f"{label}.time.log"
    result = subprocess.run(
        ["/usr/bin/time", "-v", "-o", str(time_log), *command], cwd=kit, env=env,
        text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
    )
    (kit / "results" / f"{label}.log").write_text(result.stdout)
    return {"label": label, "command": command, "exit_status": result.returncode,
            "stdout": f"results/{label}.log", "time_log": f"results/{label}.time.log"}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--kit", type=Path, default=Path(__file__).resolve().parent)
    args = parser.parse_args()
    kit = args.kit.resolve()
    results = kit / "results"
    results.mkdir(exist_ok=False)
    inputs = {name: digest(kit / name) for name in EXPECTED}
    mismatches = {name: (EXPECTED[name], actual) for name, actual in inputs.items()
                  if actual != EXPECTED[name]}
    if mismatches:
        raise SystemExit(f"input SHA-256 mismatch: {mismatches}")

    env = os.environ.copy()
    env["PATH"] = "/home/dombarker/.cargo/bin:/usr/bin:/bin"
    env["RUSTUP_TOOLCHAIN"] = "nightly-2026-06-01"
    binary = results / "wide-parser-differential-tests"
    commands = []

    def save_run():
        run = {"toolchain": "nightly-2026-06-01",
               "rustc_commit_hash_expected": EXPECTED_RUSTC_COMMIT,
               "inputs": inputs, "commands": commands,
               "coverage": {"lengths_inclusive": [0, 64],
                            "single_byte_values": 256,
                            "single_byte_positions": 32,
                            "limb_boundaries": [0, 1, "P-1", "P", "P+1", "u32::MAX"],
                            "pairwise_boundary_limb_combinations": True,
                            "seeded_random_vectors_per_length": 256,
                            "canonical_eight_limb_vectors": 4096},
               "expected_input_vectors": 30055,
               "expected_parser_calls": 60110}
        (results / "run.json").write_text(json.dumps(run, indent=2) + "\n")

    version = run_timed("rustc-version", [
        "rustup", "run", "nightly-2026-06-01", "rustc", "--version", "--verbose"
    ], kit, env)
    commands.append(version)
    save_run()
    if version["exit_status"]:
        raise SystemExit(f"pinned rustc version command failed: {version['exit_status']}")
    version_text = (results / "rustc-version.log").read_text()
    if f"commit-hash: {EXPECTED_RUSTC_COMMIT}" not in version_text:
        raise SystemExit("pinned rustc commit hash mismatch; see results/rustc-version.log")

    commands.append(run_timed("compile", [
        "rustup", "run", "nightly-2026-06-01", "rustc", "--test", "--edition=2021",
        "-C", "opt-level=3", "-C", "overflow-checks=yes", "differential.rs",
        "-o", str(binary),
    ], kit, env))
    save_run()
    if commands[-1]["exit_status"] == 0:
        commands.append(run_timed("test", [str(binary), "--exact", TEST,
                                             "--nocapture", "--test-threads=1"], kit, env))
        save_run()
    return max(c["exit_status"] for c in commands)


if __name__ == "__main__":
    sys.exit(main())
