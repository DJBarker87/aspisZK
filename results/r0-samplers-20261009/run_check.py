#!/usr/bin/env python3
"""Run a focused local check with a 6 GiB aggregate-RSS stop and evidence.

This macOS development runner is for small checks only, not a substitute for
the required Linux cgroup for large builds. Samples the whole process group.
Usage: python3 .../run_check.py NAME COMMAND [ARG ...]
"""
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
LIMIT_KIB = 6 * 1024**2


def main():
    name, *command = sys.argv[1:]
    env = dict(os.environ, CARGO_BUILD_JOBS="2", CARGO_TARGET_DIR=str(ROOT.parent.parent / "target/r0-rb"))
    files = [ROOT / "Cargo.lock", ROOT / "crates/aspis-core/Cargo.toml",
             ROOT / "crates/aspis-core/src/lib.rs", ROOT / "crates/aspis-core/src/r0_transcript.rs",
             ROOT / "crates/aspis-core/src/r0_transcript/tests.rs", HERE / "kats.json"]
    source_hashes = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files}
    revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
    start = time.monotonic()
    peak = 0
    stopped = None
    with (HERE / f"{name}.log").open("w") as log:
        child = subprocess.Popen(command, cwd=ROOT, env=env, stdout=log, stderr=subprocess.STDOUT, start_new_session=True)
        while child.poll() is None:
            processes = subprocess.check_output(["ps", "-axo", "pid=,pgid=,rss="], text=True)
            rss = sum(int(line.split()[2]) for line in processes.splitlines() if int(line.split()[1]) == child.pid)
            peak = max(peak, rss)
            if rss >= LIMIT_KIB or time.monotonic() - start > 480:
                stopped = "aggregate RSS cap" if rss >= LIMIT_KIB else "8-minute review limit"
                os.killpg(child.pid, signal.SIGKILL)
                break
            time.sleep(0.1)
        code = child.wait()
    record = {"name": name, "command": command, "exit_status": code,
              "wall_seconds": round(time.monotonic() - start, 3), "peak_aggregate_rss_kib_sampled": peak,
              "rss_stop_kib": LIMIT_KIB, "stopped": stopped, "base_revision": revision,
              "source_sha256_before": source_hashes, "cargo_build_jobs": 2,
              "cargo_target_dir": env["CARGO_TARGET_DIR"], "formal_axioms": "not applicable: Rust-only check"}
    with (HERE / "checks.jsonl").open("a") as output:
        output.write(json.dumps(record, sort_keys=True) + "\n")
    print((HERE / f"{name}.log").read_text(), end="")
    print(json.dumps({k: v for k, v in record.items() if k != "source_sha256_before"}, sort_keys=True))
    raise SystemExit(code if code >= 0 else 1)


if __name__ == "__main__":
    main()
