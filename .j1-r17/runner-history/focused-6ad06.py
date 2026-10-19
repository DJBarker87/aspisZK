#!/usr/bin/env python3
"""Check one staged Lean target in an already capped Linux user scope.

Imports are prebuilt, pinned inputs. This runner neither fetches nor builds
dependencies. The companion manifest records their source provenance.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import time


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path):
    return path.read_text().strip()


def main():
    if len(sys.argv) > 1 and sys.argv[1] == "--exec-lean":
        env = dict(os.environ)
        env["LEAN_PATH"] = sys.argv[2] + ":" + env.get("LEAN_PATH", "")
        os.execvpe("lean", ["lean", *sys.argv[3:]], env)
    ap = argparse.ArgumentParser()
    ap.add_argument("workspace", type=Path)
    ap.add_argument("module")
    ap.add_argument("--attempt", required=True)
    ap.add_argument("--revision", required=True)
    ap.add_argument("--lean-memory-mib", type=int, default=3500)
    args = ap.parse_args()
    work = args.workspace.resolve()
    source = work / "sources" / (args.module.replace(".", "/") + ".lean")
    objects = work / "objects"
    obj = objects / (args.module.replace(".", "/") + ".olean")
    manifest = work / "input-manifest.json"
    out = work / "runs" / args.attempt
    out.mkdir(parents=True, exist_ok=False)
    cg_rel = next(s.split(":", 2)[2] for s in
                  Path("/proc/self/cgroup").read_text().splitlines() if s.startswith("0::"))
    cg = Path("/sys/fs/cgroup") / cg_rel.lstrip("/")
    limits = {k: read(cg / k) for k in ["memory.max", "memory.high", "memory.swap.max"]}
    assert limits["memory.swap.max"] == "0", limits
    assert limits["memory.max"] != "max" and int(limits["memory.max"]) <= 8 * 2**30, limits
    assert limits["memory.high"] != "max" and int(limits["memory.high"]) < int(limits["memory.max"]), limits
    assert 0 < args.lean_memory_mib <= 6000
    assert args.lean_memory_mib * 2**20 < int(limits["memory.max"])
    runtime = Path("/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0")
    version = subprocess.check_output([str(runtime / "bin/lean"), "--version"], text=True).strip()
    assert "version 4.32.0," in version, version
    runtime_pins = {str(p): sha(p) for p in
                    [runtime / "bin/lean", *sorted((runtime / "lib/lean").glob("libleanshared*.so"))]}
    (out / "source.lean").write_bytes(source.read_bytes())
    obj.parent.mkdir(parents=True, exist_ok=True)
    # The backend lake environment already references the pinned Mathlib cache.
    # `env` does not build the library or its default targets.
    cwd = work.parent / "backend"
    cmd = ["/usr/bin/time", "-v", "-o", str(out / "time.log"),
           str(runtime / "bin/lake"), "--no-cache", "env", "python3", str(Path(__file__).resolve()),
           "--exec-lean", str(objects), "-j1", f"-M{args.lean_memory_mib}", "-R", str(work / "sources"),
           "-o", str(obj), str(source)]
    receipt = {"target": args.module, "source_revision": args.revision,
               "source_sha256": sha(source), "input_manifest_sha256": sha(manifest),
               "runner_sha256": sha(Path(__file__)), "runtime_sha256": runtime_pins,
               "lean_version": version, "command": cmd, "cwd": str(cwd),
               "cgroup": str(cg), "limits": limits,
               "started_utc": datetime.now(timezone.utc).isoformat(),
               "memory_events_before": read(cg / "memory.events"),
               "axioms_log": "lean.log", "dependency_rebuild": False}
    (out / "preflight.json").write_text(json.dumps(receipt, indent=2) + "\n")
    begin, peak, stopped = time.monotonic(), 0, False
    with (out / "lean.log").open("w") as log:
        proc = subprocess.Popen(cmd, cwd=cwd, stdout=log, stderr=subprocess.STDOUT,
                                start_new_session=True)
        while proc.poll() is None:
            peak = max(peak, int(read(cg / "memory.current")))
            if time.monotonic() - begin >= 600:
                os.killpg(proc.pid, signal.SIGKILL)
                stopped = True
                break
            time.sleep(0.2)
        rc = proc.wait()
    receipt.update(exit_status=rc, wall_seconds=round(time.monotonic() - begin, 3),
                   sampled_cgroup_peak_bytes=peak,
                   cgroup_memory_peak=read(cg / "memory.peak"),
                   cgroup_swap_current=read(cg / "memory.swap.current"),
                   memory_events_after=read(cg / "memory.events"),
                   stopped_at_ten_minutes_without_target=stopped,
                   olean_sha256=sha(obj) if rc == 0 and obj.is_file() else None)
    (out / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps(receipt, indent=2), flush=True)
    print((out / "lean.log").read_text()[-18000:], flush=True)
    return rc or 0


if __name__ == "__main__":
    sys.exit(main())
