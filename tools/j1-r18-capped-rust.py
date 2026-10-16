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
p.add_argument("mode", choices=["sbf", "counter", "replay"])
a = p.parse_args()
w = a.workspace.resolve()
source = w / a.source_label
manifest = w / (a.source_label + "-manifest.json")
pins = json.loads(manifest.read_text())
sha = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
for path, digest in pins["files"].items():
    assert sha(source / path) == digest, path
# Cargo fingerprints use relative paths and mtimes. Two archived workspaces
# sharing a private target cache can otherwise reuse the first workspace's
# binary when both archives predate that binary. Preserve bytes and explicitly
# make workspace inputs newer than the cache before invoking Cargo.
freshness_ns = time.time_ns()
for path in pins["files"]:
    os.utime(source / path, ns=(freshness_ns, freshness_ns))
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
    artifact = w / (a.label + "-artifacts")
    artifact.mkdir(exist_ok=False)
    command = [sol + "/cargo-build-sbf", "--manifest-path", str(source / "programs/r1-cost-probe/Cargo.toml"),
               "--sbf-out-dir", str(artifact), "--features", "pool-adapter,private-leaf-salts",
               "--tools-version", "v1.52", "--skip-tools-install", "--offline", "--", "--locked", "-j", "1"]
elif a.mode == "counter":
    command = ["/home/dombarker/.cargo/bin/cargo", "test", "--release", "--locked", "--offline",
               "-p", "aspis-r1-cost-probe-program", "--lib", "--features", "pool-adapter,private-leaf-salts",
               "--jobs", "1", "measured_core_call_counts_include_zero_progress_checkpoint", "--", "--test-threads=1"]
else:
    binary = Path("/home/dombarker/project-offloads/aspis-r1-r18-prefix-20261016/cargo-target/release/r18_replay")
    assert sha(binary) == "e40b5bf5651a3b9bf0b872dacb257e0007a29094679ed47b9b13dade22e0a5be"
    before = w / "before-sbf/aspis_r1_cost_probe_program.so"
    after = w / "after-sbf-fresh-artifacts/aspis_r1_cost_probe_program.so"
    assert sha(before) != sha(after), "refusing identical cached before/after artifacts"
    fixture = source / "docs/research/100bit-spend-path-20261013/evidence/p3-private-leaf-salts-20261013/p3-pool-13/transfer-1023-os-task"
    env.update(ASPIS_R18_BEFORE_REVISION=json.loads((w / "before-manifest.json").read_text())["revision"],
               ASPIS_R18_AFTER_REVISION=pins["revision"],
               ASPIS_R18_BEFORE_BUILD_RECEIPT=str(w / "runs/before-sbf/receipt.json"),
               ASPIS_R18_AFTER_BUILD_RECEIPT=str(w / "runs/after-sbf-fresh/receipt.json"),
               ASPIS_SOURCE_REVISION="882e4b21c555e2321101a1d00527140c043a03bd")
    command = [str(binary), str(before), str(after), str(fixture / "r1-s2-proof.bin"),
               str(fixture / "r1-s2-public-asf8.bin"), str(w / "cu-comparison-1")]
timed = ["/usr/bin/time", "-v", "-o", str(out / "time.log"), *command]
record = {"label": a.label, "mode": a.mode, "source_revision": pins["revision"],
          "workspace_source_freshness_ns": freshness_ns,
          "source_manifest_sha256": sha(manifest), "runner_sha256": sha(Path(__file__)),
          "command": timed, "cwd": str(source), "cgroup": str(cg), "limits": limits,
          "events_before": read("memory.events"), "start_unix": time.time(),
          "rustc_version": subprocess.check_output(["rustc", "-Vv"], env=env, text=True),
          "cargo_version": subprocess.check_output(["cargo", "-V"], env=env, text=True),
          "cargo_build_sbf_sha256": sha(Path(sol) / "cargo-build-sbf"),
          "environment": {k: env[k] for k in ["PATH", "CARGO_TARGET_DIR", "CARGO_BUILD_JOBS", "CARGO_NET_OFFLINE", "ASPIS_SOURCE_REVISION"]},
          "expected_work": {"counter": "cached optimized compilation and one saved-proof test",
                            "sbf": "cached optimized SBF compilation and linking; no proof generation",
                            "replay": "one before/after direct admitted-route CU pair; no proof generation"}[a.mode],
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
