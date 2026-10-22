#!/usr/bin/env python3
"""Run the existing cached Aeneas candidate on the transformed LLBC, bounded."""

from __future__ import annotations

import contextlib
import fcntl
import hashlib
import io
import json
import os
import re
import runpy
import subprocess
import time
from pathlib import Path

BASE = Path("/home/dombarker/project-offloads/s4-stdlib-fromfn-isolation-v1-20261021")
TOOL = BASE / "tool-candidate/aeneas-src"
INPUT = Path("/home/dombarker/project-offloads/d18-aeneas-reborrow-v1-20261022/input/from_fn.llbc")
OUT = Path("/home/dombarker/project-offloads/d18-aeneas-reborrow-v1-20261022/run-positive-v1")
COLLECTOR = Path("/home/dombarker/project-offloads/r1-circle-sample-wrapper-extraction-v2/collect-cgroups.py")
LOCK = Path("/tmp/aspis-global-extraction-admission-20261019.lock")
COLLECTOR_SHA = "4fc152ea4f88742fb460c301ae17446f1d1ba9162acdaafb37d80e60c4907800"
INPUT_SHA = "32f4b2416a2566ab2ceb6bd04f10a1b601e765fab9217a4fe3501cab0b0340a4"
BINARY_SHA = "ed15492916983e37d8e104a31c7f2359c8ebdebb7e4e76cacf5828ad20e74a04"
IMAGE = "sha256:ef96e46342a4159b6a62663e1ff5474a5f5deaf260daf08ea7b0963974418db7"
HIGH, MAX = 1024**3, 2 * 1024**3
G = 1024**3


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> int:
    assert INPUT.is_file() and sha(INPUT) == INPUT_SHA
    assert sha(COLLECTOR) == COLLECTOR_SHA
    binary = TOOL / "_build/default/main.exe"
    assert binary.is_file() and sha(binary) == BINARY_SHA
    assert not OUT.exists(), f"refusing to overwrite {OUT}"
    OUT.mkdir(parents=True)
    unit = re.sub(r"[^a-zA-Z0-9_.-]", "-", f"d18-reborrow-{os.getpid()}-{time.time_ns()}")

    with LOCK.open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        captured = io.StringIO()
        with contextlib.redirect_stdout(captured):
            runpy.run_path(str(COLLECTOR))
        inventory = json.loads(captured.getvalue())
        finite = inventory["effective_sum_bytes"]
        checks = {
            "finite_plus_scope_and_nested_docker_caps_le_48GiB": finite + 2 * MAX <= 48 * G,
            "MemAvailable_at_least_14GiB": inventory["MemAvailable_kB"] * 1024 >= 14 * G,
        }
        cmd = [
            "systemd-run", "--user", "--scope", "--quiet", "--unit=" + unit,
            "-p", "MemoryHigh=" + str(HIGH), "-p", "MemoryMax=" + str(MAX),
            "-p", "MemorySwapMax=0", "-p", "TasksMax=128",
            "docker", "run", "--rm", "--name", unit,
            "--memory=" + str(MAX), "--memory-swap=" + str(MAX), "--cpus=2",
            "--pids-limit=128", "--user", "1000:1000",
            "--mount", f"type=bind,src={TOOL},dst=/work",
            "--mount", f"type=bind,src={INPUT.parent},dst=/input,readonly",
            "--mount", f"type=bind,src={OUT},dst=/output",
            "--workdir", "/work", "--entrypoint", "opam", IMAGE,
            "exec", "--", "/usr/bin/time", "-v", "-o", "/output/time.log",
            "/work/_build/default/main.exe", "-sequential", "-no-progress-bar",
            "-abort-on-error", "-backend", "lean", "-namespace", "AspisFromFnReborrow",
            "-dest", "/output/generated", "-subdir", "AspisFromFnReborrow",
            "-split-files", "-emit-json", "/input/from_fn.llbc",
        ]
        admission = {
            "inventory": inventory,
            "checks": checks,
            "limits": {"memory.high": str(HIGH), "memory.max": str(MAX), "memory.swap.max": "0"},
            "input_sha256": sha(INPUT),
            "candidate_binary_sha256": sha(binary),
            "candidate_tool_source_sha256": "1f1b6527bce296728cce288648e6b5f6aa4fd0f1387a06af33fee2642244b616",
            "scope": unit + ".scope",
            "command": cmd,
        }
        (OUT / "admission.json").write_text(json.dumps(admission, indent=2) + "\n")
        print(json.dumps({"finite_reserved_GiB": finite / G, "checks": checks, "scope": unit + ".scope"}), flush=True)
        if not all(checks.values()):
            return 75

        start = time.monotonic()
        with (OUT / "stdout.log").open("x") as stdout:
            process = subprocess.Popen(cmd, stdout=stdout, stderr=subprocess.STDOUT)
        registration = None
        deadline = time.monotonic() + 10
        while time.monotonic() < deadline:
            if process.poll() is not None:
                break
            state = subprocess.run(
                ["systemctl", "--user", "show", unit + ".scope", "--property=ControlGroup", "--value"],
                text=True, capture_output=True,
            )
            cg_rel = state.stdout.strip()
            if state.returncode == 0 and cg_rel:
                cg = Path("/sys/fs/cgroup") / cg_rel.lstrip("/")
                try:
                    limits = {key: (cg / key).read_text().strip() for key in ("memory.high", "memory.max", "memory.swap.max")}
                    populated = "populated 1" in (cg / "cgroup.events").read_text()
                except FileNotFoundError:
                    time.sleep(0.02)
                    continue
                if limits == admission["limits"] and populated:
                    registration = {"control_group": cg_rel, "limits": limits, "populated": True}
                    break
            time.sleep(0.02)
        if registration is None and process.poll() is None:
            subprocess.run(["systemctl", "--user", "kill", "--signal=TERM", unit + ".scope"], capture_output=True)
            process.wait()
            raise RuntimeError("could not verify the owned scope limits; candidate terminated")
        admission["registration"] = registration
        (OUT / "admission.json").write_text(json.dumps(admission, indent=2) + "\n")
        fcntl.flock(lock, fcntl.LOCK_UN)
        code = process.wait()

    timing = (OUT / "time.log").read_text() if (OUT / "time.log").exists() else ""
    def metric(label: str):
        match = re.search(re.escape(label) + r":\s*(\d+)", timing)
        return int(match.group(1)) if match else None
    generated = [str(p.relative_to(OUT)) for p in OUT.rglob("*") if p.is_file() and p.name not in {"receipt.json", "admission.json"}]
    receipt = {
        "exit_status": code,
        "wall_seconds": time.monotonic() - start,
        "max_rss_kib": metric("Maximum resident set size (kbytes)"),
        "swap_events_reported_by_time": metric("Swaps"),
        "scope_swap_max_bytes": 0,
        "limits": registration["limits"] if registration else None,
        "input_sha256": INPUT_SHA,
        "candidate_binary_sha256": BINARY_SHA,
        "generated_files": generated,
        "command": cmd,
        "scope": unit + ".scope",
    }
    for path in OUT.rglob("*"):
        if path.is_file() and path.name not in {"receipt.json", "admission.json"}:
            receipt.setdefault("output_sha256", {})[str(path.relative_to(OUT))] = sha(path)
    (OUT / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps(receipt), flush=True)
    return code


if __name__ == "__main__":
    raise SystemExit(main())
