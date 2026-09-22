#!/usr/bin/env python3
"""Build the separate R20 LiteSVM probe with a bounded offline Cargo call.

The caller supplies a fresh probe Cargo project containing `r20_svm_probe.rs`
and the pinned dependency lockfile. This helper never edits the accepted R19
driver, SBF stage, fixtures, or shared Cargo target caches.
"""
import argparse
import hashlib
import json
import os
import shutil
import subprocess
from pathlib import Path

parser = argparse.ArgumentParser()
parser.add_argument("--project", type=Path, required=True)
parser.add_argument("--target-dir", type=Path, required=True)
parser.add_argument("--output", type=Path, required=True)
args = parser.parse_args()
project = args.project.resolve()
target = args.target_dir.resolve()
output = args.output.resolve()
assert project.is_dir() and (project / "Cargo.toml").is_file()
assert target != project and not project in target.parents
assert not output.exists()

env = os.environ.copy()
env.update(NO_DNA="1", CARGO_TARGET_DIR=str(target))
env["PATH"] = "/home/dombarker/.cargo/bin:/usr/bin:/bin:" + env.get("PATH", "")
cmd = [
    "/home/dombarker/.cargo/bin/cargo", "build", "--release", "--offline", "--locked",
    "--jobs", "2", "--manifest-path", str(project / "Cargo.toml"),
]
subprocess.run(cmd, cwd=project, env=env, check=True)
binary = target / "release" / "r20-svm-probe"
assert binary.is_file(), binary
shutil.copy2(binary, output)
print(json.dumps({
    "command": "NO_DNA=1 cargo build --release --offline --jobs 2",
    "binary": str(output),
    "binary_sha256": hashlib.sha256(output.read_bytes()).hexdigest(),
    "built": True,
    "measurements_run": False,
}))
