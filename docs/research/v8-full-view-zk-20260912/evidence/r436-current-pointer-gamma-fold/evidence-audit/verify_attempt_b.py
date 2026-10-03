#!/usr/bin/env python3
"""Read-only custody verifier for the saved R436 attempt B compile."""
from pathlib import Path
import hashlib, json, re

HERE = Path(__file__).resolve().parent.parent
A, B = HERE / "attempt-a", HERE / "attempt-b"
ROOT_SOURCE = HERE / "R436PointerGammaFold.UNVERIFIED.lean"
FOUNDATIONS = {"propext", "Classical.choice", "Quot.sound"}

def need(ok, msg):
    if not ok: raise SystemExit("FAIL: " + msg)
def js(d, n): return json.loads((d/n).read_text())
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()

receipt = js(B, "receipt.json")
source = B / "source.lean"
need(ROOT_SOURCE.read_bytes() == source.read_bytes(), "root source is not byte-identical to B input")
need(sha(source) == receipt["source_sha256"] == js(B, "host-after.json")["source_sha256"], "B source SHA mismatch")
need(receipt["target"] == "AspisV8R19/R436PointerGammaFold.lean", "target mismatch")
need(receipt["source_revision"] == "77857d6028d1b4016949aa14b19c17282e2cec0c", "revision mismatch")
need(receipt["exit_status"] == 0, "B exit status is not successful")
need("4.32.0" in receipt["lean_version"] and "8c9756b28d64dab099da31a4c09229a9e6a2ef35" in receipt["lean_version"], "Lean toolchain mismatch")

log = (B/"lean.log").read_text()
reports = [line for line in log.splitlines() if line.startswith("'AspisV8R19.R436PointerGammaFold.") and ("depends on axioms:" in line or "does not depend on any axioms" in line)]
need(len(reports) == 1 and reports == receipt["complete_print_axioms"], "B complete axiom output differs from receipt")
need(source.read_text().count("#print axioms") == 1, "B source axiom-print request count mismatch")
for line in reports:
    names = set(re.findall(r"\b(?:propext|Classical\.choice|Quot\.sound|sorryAx)\b", line))
    need("sorryAx" not in names and names <= FOUNDATIONS, "unexpected axiom in B report")

gnu = (B/"gnu-time.txt").read_text()
for pattern, expected, cast in [
    (r"Elapsed \(wall clock\) time \(h:mm:ss or m:ss\):\s*(\S+)", receipt["wall_time"], str),
    (r"Maximum resident set size \(kbytes\):\s*(\d+)", receipt["peak_rss_kib"], int),
    (r"Swaps:\s*(\d+)", receipt["swaps"], int),
    (r"Exit status:\s*(\d+)", receipt["exit_status"], int),
]:
    m = re.search(pattern, gnu)
    need(m is not None and cast(m.group(1)) == expected, "GNU time/receipt mismatch")
need(receipt["swaps"] == 0 and js(B, "launch-status.json")["ssh_exit_status"] == 0, "B swap/launch status mismatch")

limits = {"memory.high":"5368709120", "memory.max":"7516192768", "memory.swap.max":"0", "pids.max":"128"}
before, after = js(B,"host-before.json")["cgroup"], js(B,"host-after.json")["cgroup"]
for label, snap in (("before",before),("after",after)):
    need(all(snap.get(k)==v for k,v in limits.items()), f"{label} cgroup cap mismatch")
    events=dict(row.split() for row in snap["memory.events"].splitlines())
    need(all(events.get(k)=="0" for k in ("high","max","oom","oom_kill","oom_group_kill")), f"{label} cgroup event")
need(after["memory.swap.peak"]=="0" and js(B,"host-after.json")["olean_sha256"], "B swap/OLean receipt mismatch")
copies=sorted(B.glob("*.copy-status.json"))
need(len(copies)==6, f"expected six copy receipts, found {len(copies)}")
for p in copies: need(js(B,p.name).get("exit_status")==0, f"copy failed: {p.name}")

receipt_a=js(A,"receipt.json")
log_a=(A/"lean.log").read_text()
need(receipt_a["exit_status"]==1 and "No goals to be solved" in log_a, "A's rejected trailing-rfl failure missing")
need("sorryAx" not in log_a, "A failure history differs from expected (A failed despite standard-only axiom output)")

report={
    "status":"PASS",
    "target":receipt["target"],
    "source_revision":receipt["source_revision"],
    "source_sha256":receipt["source_sha256"],
    "root_source_equals_attempt_b":True,
    "exit_status":receipt["exit_status"],
    "wall_time":receipt["wall_time"],
    "gnu_peak_rss_kib":receipt["peak_rss_kib"],
    "swaps":receipt["swaps"],
    "complete_axiom_reports":len(reports),
    "axiom_whitelist":sorted(FOUNDATIONS),
    "effective_cgroup_limits":limits,
    "cgroup_memory_peak_bytes":int(after["memory.peak"]),
    "copy_status_count":len(copies),
    "attempt_a":{"exit_status":receipt_a["exit_status"],"rejected_error":"No goals to be solved after rewrite closed the goal","sorryAx_in_failed_output":False},
    "boundary":"Model composition only; no actual Rust source correspondence or native execution-closure claim."
}
print(json.dumps(report,indent=2))
