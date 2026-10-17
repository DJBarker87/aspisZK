#!/usr/bin/env python3
"""Launch one optimized actual-S2 injection gate in a capped Linux scope."""
import argparse
import json
from pathlib import Path
import subprocess
import sys
import time

ap = argparse.ArgumentParser(description=__doc__)
ap.add_argument("--root", type=Path, required=True)
ap.add_argument("--detail", choices=["true", "false"], required=True)
args = ap.parse_args()
p = args.root
label = "verify-real-s2-" + ("detail" if args.detail == "true" else "default")
inputs = json.loads((p / "inputs.json").read_text())
reservations = []
for directory in Path("/sys/fs/cgroup").rglob("*.scope"):
    try:
        maximum = (directory / "memory.max").read_text().strip()
        if maximum != "max" and "populated 1" in (directory / "cgroup.events").read_text():
            reservations.append({"scope": str(directory), "memory_max_bytes": int(maximum)})
    except (FileNotFoundError, PermissionError):
        pass
current = sum(item["memory_max_bytes"] for item in reservations)
reservation = {"time_unix": time.time(), "active_scope_reservations": reservations,
    "existing_scope_max_total_bytes": current, "new_scope_memory_max_bytes": 8 * 2**30,
    "total_with_new_bytes": current + 8 * 2**30, "safe_working_limit_bytes": 55 * 2**30,
    "expected_work": "warm optimized native compilation, then named finite actual-S2 failure gate; no proof generation",
    "source_revision": inputs["source_revision"], "Lean_job": False, "SBF_build": False}
with (p / (label + "-reservation.json")).open("x") as out:
    json.dump(reservation, out, indent=2)
    out.write("\n")
assert reservation["total_with_new_bytes"] < reservation["safe_working_limit_bytes"], reservation
features = "prover,private-leaf-salts,optimized-terminal"
if args.detail == "true":
    features += ",detail-phases"
gate = ["/home/dombarker/.cargo/bin/cargo", "test", "--verbose", "--release", "--locked", "--offline", "-j1",
    "-p", "aspis-r1-cost-probe", "--features", features, "--lib",
    "r1_semantic::verify_migration_tests::verify_saved_s2_exact_old_new_all_round_failures_and_success",
    "--", "--nocapture", "--test-threads=1"]
command = ["systemd-run", "--user", "--scope", "--quiet", "--unit=r1-root-" + label + "-20261017",
    "-p", "MemoryHigh=6G", "-p", "MemoryMax=8G", "-p", "MemorySwapMax=0", "python3",
    str(p / "run-final-host.py"), "--root", str(p), "--input-manifest", str(p / "inputs.json"),
    "--label", label, "--cwd", str(p / "source"), "--kind", "native", "--timeout", "600", "--", *gate]
print(json.dumps({"label": label, "reservation_bytes": reservation["total_with_new_bytes"],
    "safe_limit_bytes": reservation["safe_working_limit_bytes"]}), flush=True)
sys.exit(subprocess.run(command).returncode)
