#!/usr/bin/env python3
"""One focused prefix/suffix field-map theorem under the admitted NUC scope."""
from pathlib import Path
import hashlib, json, os, re, subprocess, time

W = Path(__file__).resolve().parent
C = json.loads((W / "config.json").read_text())
P = W / "proofs" / "PrefixSuffixAlphaBridge.lean"
OUT = W / "runs" / "bridge"
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(P) == C["bridge_source_sha256"]
assert C["scope_memory_high_bytes"] == 512 * 2**20
assert C["scope_memory_max_bytes"] == 2 * 2**30

cgline = Path("/proc/self/cgroup").read_text().strip()
assert cgline.startswith("0::")
cg = Path("/sys/fs/cgroup") / cgline[3:].lstrip("/")
limits = {n: (cg / n).read_text().strip() for n in
          ["memory.high", "memory.max", "memory.swap.max"]}
assert limits == {"memory.high": str(512*2**20),
                  "memory.max": str(2*2**30), "memory.swap.max": "0"}, limits

def first_hit(rel):
    hits = [Path(r) / rel for r in C["lean_path"] if (Path(r) / rel).is_file()]
    assert hits, rel
    return hits[0], sha(hits[0])

selected = {}
for rel, wanted in C["expected_imports"].items():
    path, got = first_hit(rel)
    assert got == wanted, (rel, str(path), got, wanted)
    selected[rel] = {"path": str(path), "sha256": got}

OUT.mkdir(parents=True, exist_ok=False)
obj = W / "attempt" / "objects"
obj.mkdir(parents=True, exist_ok=True)
env = dict(os.environ)
env["LEAN_PATH"] = ":".join([str(obj), *C["lean_path"]])
cmd = [C["lean"], "-M4400", "-j1", "-R", str(W / "proofs"),
       "-o", str(obj / "PrefixSuffixAlphaBridge.olean"), str(P)]
before = (cg / "memory.events").read_text()
start = time.monotonic()
timing = OUT / "time.log"
with (OUT / "lean.log").open("x") as log:
    p = subprocess.Popen(["/usr/bin/time", "-v", "-o", str(timing), *cmd],
                         cwd=W / "proofs", env=env, stdout=log,
                         stderr=subprocess.STDOUT, start_new_session=True)
    peak = 0
    while p.poll() is None:
        peak = max(peak, int((cg / "memory.current").read_text()))
        if time.monotonic() - start > 120:
            p.terminate()
            p.wait()
            break
        time.sleep(.2)
    p.wait()
t = timing.read_text() if timing.exists() else ""
def num(label):
    m = re.search(re.escape(label) + r":\s*(\d+)", t)
    return int(m[1]) if m else None
receipt = {
    "phase": "bridge", "exit_status": p.returncode,
    "wall_seconds": time.monotonic()-start,
    "peak_process_rss_kib": num("Maximum resident set size (kbytes)"),
    "process_swaps": num("Swaps"), "sampled_cgroup_peak_bytes": peak,
    "cgroup_peak_bytes": int((cg / "memory.peak").read_text()),
    "cgroup_swap_current": int((cg / "memory.swap.current").read_text()),
    "memory_events_before": before, "memory_events_after": (cg / "memory.events").read_text(),
    "limits": limits, "command": cmd, "lean_path": env["LEAN_PATH"],
    "source_sha256": sha(P), "selected_imports": selected,
    "output_sha256": sha(obj / "PrefixSuffixAlphaBridge.olean") if p.returncode == 0 else None,
    "scope": "Conditional generated-prefix success and prepared-suffix success; no full-resume reachability claim.",
    "axioms_expected": "[propext, Classical.choice, Quot.sound]",
}
(OUT / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
print(json.dumps(receipt), flush=True)
raise SystemExit(p.returncode)
