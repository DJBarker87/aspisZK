#!/usr/bin/env python3
"""Run one source-pinned R18 Rust target in a verified 8/10 GiB scope.

The caller supplies a private workspace and an immutable source manifest.
No compilation is launched before checking the actual process cgroup.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import time

p = argparse.ArgumentParser()
p.add_argument("workspace", type=Path)
p.add_argument("label")
p.add_argument("source_label", choices=["before", "after"])
p.add_argument("mode", choices=["sbf", "counter"])
a = p.parse_args()
w = a.workspace.resolve()
source = w / a.source_label
manifest = w / (a.source_label + "-manifest.json")
pins = json.loads(manifest.read_text())
sha = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
for path, digest in pins["files"].items():
    assert sha(source / path) == digest, path
cg = Path("/sys/fs/cgroup") / next(
    line.split(":", 2)[2]
    for line in Path("/proc/self/cgroup").read_text().splitlines()
    if line.startswith("0::")
).lstrip("/")
read = lambda name: (cg / name).read_text().strip()
limits = {name: read(name) for name in ["memory.high", "memory.max", "memory.swap.max"]}
assert limits == {"memory.high": "8589934592", "memory.max": "10737418240", "memory.swap.max": "0"}, limits
out = w / "runs" / a.label
out.mkdir(parents=True, exist_ok=False)
(out / "runner.py").write_bytes(Path(__file__).read_bytes())
sol = "/home/dombarker/.local/share/solana/install/releases/3.1.13/solana-release/bin"
env = dict(os.environ, PATH=sol + ":/home/dombarker/.cargo/bin:/usr/bin:/bin",
           CARGO_TARGET_DIR=str(w / "cargo-target"), CARGO_BUILD_JOBS="1",
           CARGO_NET_OFFLINE="true", ASPIS_SOURCE_REVISION=pins["revision"])
for name in ["RUSTFLAGS", "RUSTC_WRAPPER", "RUSTC_WORKSPACE_WRAPPER", "CARGO_ENCODED_RUSTFLAGS"]:
    env.pop(name, None)
if a.mode == "sbf":
    artifact = w / (a.source_label + "-sbf")
    artifact.mkdir(exist_ok=False)
    command = [sol + "/cargo-build-sbf", "--manifest-path", str(source / "programs/r1-cost-probe/Cargo.toml"),
               "--sbf-out-dir", str(artifact), "--features", "pool-adapter,private-leaf-salts",
               "--tools-version", "v1.52", "--skip-tools-install", "--offline", "--", "--locked", "-j", "1"]
else:
    command = ["/home/dombarker/.cargo/bin/cargo", "test", "--release", "--locked", "--offline",
               "-p", "aspis-r1-cost-probe-program", "--lib", "--features", "pool-adapter,private-leaf-salts",
               "--jobs", "1", "measured_core_call_counts_include_zero_progress_checkpoint", "--", "--test-threads=1"]
timed = ["/usr/bin/time", "-v", "-o", str(out / "time.log"), *command]
record = {"label": a.label, "mode": a.mode, "source_revision": pins["revision"],
          "source_manifest_sha256": sha(manifest), "runner_sha256": sha(Path(__file__)),
          "command": timed, "cwd": str(source), "cgroup": str(cg), "limits": limits,
          "events_before": read("memory.events"), "start_unix": time.time(),
          "rustc_version": subprocess.check_output(["rustc", "-Vv"], env=env, text=True),
          "cargo_version": subprocess.check_output(["cargo", "-V"], env=env, text=True),
          "cargo_build_sbf_sha256": sha(Path(sol) / "cargo-build-sbf"),
          "environment": {k: env[k] for k in ["PATH", "CARGO_TARGET_DIR", "CARGO_BUILD_JOBS", "CARGO_NET_OFFLINE", "ASPIS_SOURCE_REVISION"]},
          "expected_work": "cached optimized compilation and one saved-proof test" if a.mode == "counter" else "cached optimized SBF compilation and linking; no proof generation",
          "axioms": "not applicable: Rust execution evidence, no Lean theorem"}
(out / "preflight.json").write_text(json.dumps(record, indent=2) + "\n")
start = time.monotonic()
peak = 0
with (out / "build.log").open("w") as log:
    process = subprocess.Popen(timed, cwd=source, env=env, stdout=log, stderr=subprocess.STDOUT, start_new_session=True)
    while process.poll() is None:
        peak = max(peak, int(read("memory.current")))
        if time.monotonic() - start > 600:
            os.killpg(process.pid, signal.SIGKILL)
            record["timeout"] = "600-second review point; no automatic rerun"
            break
        time.sleep(0.2)
    process.wait()
record.update(exit=process.returncode, wall_seconds=time.monotonic() - start,
              sampled_peak_bytes=peak, cgroup_peak_bytes=int(read("memory.peak")),
              swap_current_bytes=int(read("memory.swap.current")), events_after=read("memory.events"))
if a.mode == "sbf":
    record["artifacts"] = {str(path.relative_to(w)): sha(path) for path in artifact.iterdir() if path.suffix == ".so"}
    record["keys_retained"] = True
(out / "receipt.json").write_text(json.dumps(record, indent=2) + "\n")
print(json.dumps({key: record[key] for key in ["label", "exit", "wall_seconds", "cgroup_peak_bytes", "swap_current_bytes"]}), flush=True)
print((out / "build.log").read_text()[-5000:], flush=True)
raise SystemExit(process.returncode)
