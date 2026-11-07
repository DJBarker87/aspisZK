#!/usr/bin/env python3
"""Run a named focused job inside the caller's already-capped systemd scope."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--label", required=True)
    parser.add_argument("--cwd", type=Path, required=True)
    parser.add_argument("--timeout", type=int, default=180)
    parser.add_argument("command", nargs=argparse.REMAINDER)
    args = parser.parse_args()
    command = args.command[1:] if args.command[:1] == ["--"] else args.command
    assert command
    cgroup_line = Path("/proc/self/cgroup").read_text().strip()
    assert cgroup_line.startswith("0::")
    cgroup = Path("/sys/fs/cgroup") / cgroup_line[3:].lstrip("/")
    limits = {name: (cgroup / name).read_text().strip()
              for name in ["memory.high", "memory.max", "memory.swap.max"]}
    assert limits == {"memory.high": "6442450944", "memory.max": "8589934592", "memory.swap.max": "0"}, limits
    pins = json.loads((args.root / "input/source-pins.json").read_text())
    for name, digest in pins["kit_files"].items():
        assert sha(args.root / "input" / name) == digest
    out = args.root / "runs" / args.label
    out.mkdir(parents=True, exist_ok=False)
    env = dict(os.environ)
    env.update(RUSTUP_TOOLCHAIN="nightly-2026-06-01", CARGO_BUILD_JOBS="1",
               CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS="true",
               CARGO_TARGET_DIR=str(args.root / "native-target"),
               CHARON_TOOLCHAIN_IS_IN_PATH="1")
    toolchain = "/home/dombarker/.rustup/toolchains/nightly-2026-06-01-x86_64-unknown-linux-gnu/bin"
    env["PATH"] = toolchain + ":/home/dombarker/.cargo/bin:" + env.get("PATH", "")
    env["LD_LIBRARY_PATH"] = str(Path(toolchain).parent / "lib") + ":" + env.get("LD_LIBRARY_PATH", "")
    for name in ["PATH", "LD_LIBRARY_PATH", "RUSTUP_TOOLCHAIN", "CARGO_BUILD_JOBS",
                 "CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS", "CARGO_TARGET_DIR", "CHARON_TOOLCHAIN_IS_IN_PATH"]:
        assert name in env
    (out / "environment.json").write_text(json.dumps({name: env[name] for name in [
        "PATH", "LD_LIBRARY_PATH", "RUSTUP_TOOLCHAIN", "CARGO_BUILD_JOBS",
        "CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS", "CARGO_TARGET_DIR", "CHARON_TOOLCHAIN_IS_IN_PATH"]}, indent=2) + "\n")
    start = time.monotonic()
    with (out / "stdout.log").open("x") as log:
        result = subprocess.run(["/usr/bin/time", "-v", "-o", str(out / "time.log"),
                                 "timeout", "--signal=KILL", str(args.timeout), *command],
                                cwd=args.cwd, env=env, stdout=log, stderr=subprocess.STDOUT)
    elapsed = time.monotonic() - start
    timing = (out / "time.log").read_text()
    def number(label):
        match = re.search(re.escape(label) + r":\s*(\d+)", timing)
        return int(match[1]) if match else None
    receipt = {"label": args.label, "source_revision": pins["source_revision"],
               "command": command, "cwd": str(args.cwd), "exit_status": result.returncode,
               "wall_seconds": elapsed, "peak_rss_kib": number("Maximum resident set size (kbytes)"),
               "swaps": number("Swaps"), "cgroup": cgroup_line, "limits": limits,
               "memory_events": (cgroup / "memory.events").read_text(),
               "cgroup_memory_peak_bytes": int((cgroup / "memory.peak").read_text()),
               "runner_sha256": sha(Path(__file__)), "timeout_seconds": args.timeout,
               "scope": "Focused Rust/tool invocation only; no Lean/proof claim."}
    (out / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps(receipt), flush=True)
    raise SystemExit(result.returncode)

if __name__ == "__main__":
    main()
