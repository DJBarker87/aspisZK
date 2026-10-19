#!/usr/bin/env python3
"""Serial focused Lean 4.32 backend rebuild inside an existing capped scope.

No dependency fetch/build, outer lock, parallel Lean process, or fallback
toolchain. Reuses an explicitly selected, pinned Mathlib cache read-only.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
import time


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path):
    return path.read_text().strip()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("workspace", type=Path)
    ap.add_argument("--attempt", required=True)
    ap.add_argument("--target", action="append", help="Focus one root and its missing internal predecessors")
    args = ap.parse_args()
    work = args.workspace.resolve()
    backend = work / "backend"
    out = work / "runs" / args.attempt
    out.mkdir(parents=True, exist_ok=False)
    (out / "runner.py").write_bytes(Path(__file__).read_bytes())
    cg_rel = [s.split(":", 2)[2] for s in
              Path("/proc/self/cgroup").read_text().splitlines() if s.startswith("0::")][0]
    cg = Path("/sys/fs/cgroup") / cg_rel.lstrip("/")
    limits = {name: read(cg / name) for name in
              ["memory.max", "memory.high", "memory.swap.max"]}
    assert limits["memory.swap.max"] == "0", limits
    assert limits["memory.max"] != "max" and int(limits["memory.max"]) <= 8 * 2**30, limits
    assert limits["memory.high"] != "max" and int(limits["memory.high"]) < int(limits["memory.max"]), limits
    assert read(backend / "lean-toolchain") == "leanprover/lean4:v4.32.0"
    runtime = Path("/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0")
    version = subprocess.check_output([str(runtime / "bin/lean"), "--version"], text=True).strip()
    assert "version 4.32.0," in version, version
    sources = {str(p.relative_to(backend).with_suffix("")).replace("/", "."): p
               for p in backend.rglob("*.lean") if ".lake" not in p.parts and p.name != "lakefile.lean"}
    deps = {}
    for name, path in sources.items():
        imported = []
        for line in path.read_text().splitlines():
            m = re.match(r"^(?:public |private )?import\s+(?:all\s+)?(.+)$", line)
            if m:
                imported += [s for s in m[1].split("--")[0].split() if s in sources]
        deps[name] = imported
    ordered, visiting, done = [], set(), set()

    def visit(name):
        if name in done:
            return
        assert name not in visiting, name
        visiting.add(name)
        for dep in deps[name]:
            visit(dep)
        visiting.remove(name)
        done.add(name)
        ordered.append(name)

    for name in args.target or ["AeneasMeta", "Aeneas"]:
        visit(name)
    objects = backend / ".lake/build/lib/lean"
    objects.mkdir(parents=True, exist_ok=True)
    evidence = work / "successful-targets"
    evidence.mkdir(exist_ok=True)
    runtime_pins = {str(p): sha(p) for p in
                    [runtime / "bin/lean", *sorted((runtime / "lib/lean").glob("libleanshared*.so"))]}
    run = {"lean_version": version, "runtime_sha256": runtime_pins,
           "started_utc": datetime.now(timezone.utc).isoformat(),
           "cgroup": str(cg), "limits": limits,
           "memory_events_before": read(cg / "memory.events"),
           "ordered_modules": ordered,
           "input_manifest_sha256": sha(work / "input-manifest.json"),
           "runner_sha256": sha(Path(__file__)),
           "scope": "Backend only, one lake env lean target at a time; no native/exe target or axioms conclusion."}
    (out / "preflight.json").write_text(json.dumps(run, indent=2) + "\n")
    pending_reuse = []
    for index, name in enumerate(ordered):
        path = sources[name]
        stem = name.replace(".", "/")
        obj = objects / (stem + ".olean")
        key = {"source": sha(path), "imports": {dep: sha(objects / (dep.replace(".", "/") + ".olean"))
                                                  for dep in deps[name]},
               "runtime": runtime_pins, "toolchain": sha(backend / "lean-toolchain"),
               "manifest": sha(backend / "lake-manifest.json")}
        saved = evidence / (name + ".json")
        if saved.is_file() and obj.is_file():
            old = json.loads(saved.read_text())
            if old.get("key") == key and old.get("olean_sha256") == sha(obj):
                pending_reuse.append(name)
                continue
        obj.parent.mkdir(parents=True, exist_ok=True)
        target = out / name
        target.mkdir()
        (target / path.name).write_bytes(path.read_bytes())
        cmd = ["/usr/bin/time", "-v", "-o", str(target / "time.log"),
               str(runtime / "bin/lake"), "--no-cache", "env", "lean", "-j1", "-M0",
               "-R", str(backend), "-o", str(obj), str(path)]
        if pending_reuse:
            print(f"REUSE {len(pending_reuse)} unchanged predecessors", flush=True)
            pending_reuse.clear()
        print(f"START {index + 1}/{len(ordered)} {name}", flush=True)
        begin, peak, stopped = time.monotonic(), 0, False
        with (target / "lean.log").open("w") as log:
            proc = subprocess.Popen(cmd, cwd=backend, stdout=log, stderr=subprocess.STDOUT,
                                    start_new_session=True)
            while proc.poll() is None:
                peak = max(peak, int(read(cg / "memory.current")))
                if time.monotonic() - begin >= 600:
                    os.killpg(proc.pid, signal.SIGKILL)
                    stopped = True
                    break
                time.sleep(0.2)
            rc = proc.wait()
        receipt = {"target": name, "command": cmd, "cwd": str(backend), "key": key,
                   "exit_status": rc, "wall_seconds": round(time.monotonic() - begin, 3),
                   "sampled_cgroup_peak_bytes": peak, "cgroup_memory_peak": read(cg / "memory.peak"),
                   "cgroup_swap_current": read(cg / "memory.swap.current"),
                   "memory_events_after": read(cg / "memory.events"),
                   "stopped_at_ten_minutes_without_target": stopped,
                   "olean_sha256": sha(obj) if rc == 0 and obj.is_file() else None}
        timing = (target / "time.log").read_text()
        for field, label in [("peak_process_rss_kib", "Maximum resident set size (kbytes)"),
                             ("process_swaps", "Swaps")]:
            match = re.search(re.escape(label) + r":\s*(\d+)", timing)
            receipt[field] = int(match[1]) if match else None
        (target / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
        print(f"END {name} exit={rc} wall={receipt['wall_seconds']} cgroup_peak={peak}", flush=True)
        if rc != 0:
            print((target / "lean.log").read_text()[-12000:], flush=True)
            return rc or 1
        saved.write_text(json.dumps(receipt, indent=2) + "\n")
    if pending_reuse:
        print(f"REUSE {len(pending_reuse)} unchanged predecessors", flush=True)
    (out / "complete.json").write_text(json.dumps({"targets": len(ordered), "exit_status": 0}) + "\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
