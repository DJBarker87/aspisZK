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
    if len(sys.argv) > 1 and sys.argv[1] == "--exec-lean":
        env = dict(os.environ)
        pinned = json.loads(Path(sys.argv[2]).read_text())
        env.update({k:v for k,v in pinned.items() if isinstance(v,str)})
        env["LEAN_PATH"] = sys.argv[3] + ":" + env.get("LEAN_PATH", "")
        os.execvpe("lean", ["lean", *sys.argv[4:]], env)
    ap = argparse.ArgumentParser()
    ap.add_argument("workspace", type=Path)
    ap.add_argument("module")
    ap.add_argument("--attempt", required=True)
    ap.add_argument("--revision", required=True)
    ap.add_argument("--lean-memory-mib", type=int, default=0,
                    help="0 uses the mandatory cgroup limit alone; Lean's RSS counter includes shared import mappings")
    args = ap.parse_args()
    work = args.workspace.resolve()
    source = work / "sources" / (args.module.replace(".", "/") + ".lean")
    objects = work / "objects"
    obj = objects / (args.module.replace(".", "/") + ".olean")
    manifest = work / "input-manifest.json"
    out = work / "runs" / args.attempt
    out.mkdir(parents=True, exist_ok=False)
    (out / "runner.py").write_bytes(Path(__file__).read_bytes())
    cg_rel = next(s.split(":", 2)[2] for s in
                  Path("/proc/self/cgroup").read_text().splitlines() if s.startswith("0::"))
    cg = Path("/sys/fs/cgroup") / cg_rel.lstrip("/")
    limits = {k: read(cg / k) for k in ["memory.max", "memory.high", "memory.swap.max"]}
    assert limits["memory.swap.max"] == "0", limits
    assert limits["memory.max"] != "max" and int(limits["memory.max"]) <= 8 * 2**30, limits
    assert limits["memory.high"] != "max" and int(limits["memory.high"]) < int(limits["memory.max"]), limits
    assert 0 <= args.lean_memory_mib <= 6000
    assert args.lean_memory_mib * 2**20 < int(limits["memory.max"])
    reservations=[]
    for maximum in Path('/sys/fs/cgroup').rglob('memory.max'):
        try:
            v=maximum.read_text().strip()
            if v!='max' and 'populated 1' in (maximum.parent/'cgroup.events').read_text():
                reservations.append({'cgroup':str(maximum.parent),'memory_max_bytes':int(v)})
        except (OSError,PermissionError): pass
    aggregate={'populated_capped_cgroups':reservations,'total_memory_max_bytes':sum(x['memory_max_bytes'] for x in reservations),'safe_limit_bytes':55*2**30}
    assert aggregate['total_memory_max_bytes'] < aggregate['safe_limit_bytes'],aggregate
    runtime = Path("/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0")
    version = subprocess.check_output([str(runtime / "bin/lean"), "--version"], text=True).strip()
    assert "version 4.32.0," in version, version
    runtime_pins = {str(p): sha(p) for p in
                    [runtime / "bin/lean", *sorted((runtime / "lib/lean").glob("libleanshared*.so"))]}
    (out / "source.lean").write_bytes(source.read_bytes())
    obj.parent.mkdir(parents=True, exist_ok=True)
    # The backend lake environment already references the pinned Mathlib cache.
    # `env` does not build the library or its default targets.
    cwd = Path("/home/dombarker/project-offloads/aspis-r1-j17-port-20261015/backend")
    cmd = ["/usr/bin/time", "-v", "-o", str(out / "time.log"),
           str(runtime / "bin/lake"), "--no-cache", "env", "python3", str(Path(__file__).resolve()),
           "--exec-lean", str(work / "primitive-environment.json"), str(objects), "-j1", f"-M{args.lean_memory_mib}", "-R", str(work / "sources"),
           "-o", str(obj), str(source)]
    receipt = {"target": args.module, "source_revision": args.revision,
               "source_sha256": sha(source), "input_manifest_sha256": sha(manifest),
               "runner_sha256": sha(Path(__file__)), "runtime_sha256": runtime_pins,
               "lean_version": version, "command": cmd, "cwd": str(cwd),
               "cgroup": str(cg), "limits": limits,
               "started_utc": datetime.now(timezone.utc).isoformat(),
               "memory_events_before": read(cg / "memory.events"),
               "axioms_log": "lean.log", "dependency_rebuild": False,"reservation":aggregate}
    assert sha(work/'primitive-environment.json') == '19815e88217e42aaf971ba17dddf8e88cb00e1cdbd80f8cb076ec37ee490eb76'
    receipt['environment_sha256']=sha(work/'primitive-environment.json')
    (out / "preflight.json").write_text(json.dumps(receipt, indent=2) + "\n")
    def external_lean():
        found=[]
        for d in Path('/proc').iterdir():
            if not d.name.isdigit(): continue
            try:
                exe=(d/'exe').resolve().name
                group=(d/'cgroup').read_text()
                if exe=='lean' and cg_rel not in group:
                    found.append({'pid':int(d.name),'cmdline':(d/'cmdline').read_bytes().replace(b'\0',b' ').decode(errors='replace'),'cgroup':group})
            except (OSError,PermissionError): pass
        return found
    preexternal=external_lean()
    if preexternal:
        receipt.update(exit_status=78,not_launched=True,external_lean_prelaunch=preexternal,
                       result_classification='GUARD_SUPPRESSED_NO_LEAN_LAUNCHED')
        (out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
        print(json.dumps(receipt,indent=2),flush=True)
        return 78
    receipt['external_lean_prelaunch'] = preexternal
    receipt['exclusive_lean_policy'] = 'Same-launcher precheck and 200ms monitor; stop own process group if external Lean appears; never signal external.'
    begin, peak, stopped = time.monotonic(), 0, False
    overlap=[]
    with (out / "lean.log").open("w") as log:
        proc = subprocess.Popen(cmd, cwd=cwd, stdout=log, stderr=subprocess.STDOUT,
                                start_new_session=True)
        while proc.poll() is None:
            peak = max(peak, int(read(cg / "memory.current")))
            found=external_lean()
            if found:
                overlap.append({'utc':datetime.now(timezone.utc).isoformat(),'external':found})
                os.killpg(proc.pid,signal.SIGTERM)
                stopped=True
                break
            if time.monotonic() - begin >= 180:
                os.killpg(proc.pid, signal.SIGKILL)
                stopped = True
                break
            time.sleep(0.2)
        rc = proc.wait()
    receipt["external_lean_overlap"] = overlap
    receipt.update(exit_status=rc, wall_seconds=round(time.monotonic() - begin, 3),
                   sampled_cgroup_peak_bytes=peak,
                   cgroup_memory_peak=read(cg / "memory.peak"),
                   cgroup_swap_current=read(cg / "memory.swap.current"),
                   memory_events_after=read(cg / "memory.events"),
                   stopped_at_180_seconds_without_target=stopped,
                   olean_sha256=sha(obj) if rc == 0 and obj.is_file() else None)
    timing = (out / "time.log").read_text()
    for field, label in [("peak_process_rss_kib", "Maximum resident set size (kbytes)"),
                         ("process_swaps", "Swaps")]:
        match = re.search(re.escape(label) + r":\s*(\d+)", timing)
        receipt[field] = int(match[1]) if match else None
    (out / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps(receipt, indent=2), flush=True)
    print((out / "lean.log").read_text()[-18000:], flush=True)
    return rc or 0


if __name__ == "__main__":
    sys.exit(main())
