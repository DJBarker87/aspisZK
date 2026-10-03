#!/usr/bin/env python3
"""Read-only integrity check for the saved R435 attempt B Lean compile."""
from pathlib import Path
import hashlib, json, re

HERE = Path(__file__).resolve().parent.parent
A = HERE / "attempt-a"
B = HERE / "attempt-b"
ROOT_SOURCE = HERE / "R435HelperGuards.UNVERIFIED.lean"
FOUNDATIONS = {"propext", "Classical.choice", "Quot.sound"}

def need(ok, msg):
    if not ok: raise SystemExit("FAIL: " + msg)
def js(folder, name): return json.loads((folder / name).read_text())
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()

receipt = js(B, "receipt.json")
source = B / "source.lean"
need(ROOT_SOURCE.read_bytes() == source.read_bytes(), "root source differs from B source")
need(sha(source) == receipt["source_sha256"], "B source SHA differs from receipt")
need(js(B, "host-after.json")["source_sha256"] == receipt["source_sha256"], "host-after source SHA mismatch")
need(receipt["target"] == "AspisV8R19/R435HelperGuards.lean", "target mismatch")
need(receipt["source_revision"] == "f997fffc34b60ebf9a93e80b8edbdc96485ae9d6", "source revision mismatch")
need(receipt["exit_status"] == 0, "B is not a successful compilation")
need("4.32.0" in receipt["lean_version"] and "8c9756b28d64dab099da31a4c09229a9e6a2ef35" in receipt["lean_version"], "Lean toolchain pin mismatch")

log = (B / "lean.log").read_text()
reports = [line for line in log.splitlines() if line.startswith("'AspisV8R19.R435HelperGuards.") and ("depends on axioms:" in line or "does not depend on any axioms" in line)]
need(len(reports) == 4, f"expected four complete reports, got {len(reports)}")
need(reports == receipt["complete_print_axioms"], "log reports differ from receipt")
need(source.read_text().count("#print axioms") == 4, "source axiom-print request count mismatch")
for line in reports:
    names = set(re.findall(r"\b(?:propext|Classical\.choice|Quot\.sound|sorryAx)\b", line))
    need("sorryAx" not in names and names <= FOUNDATIONS, "unexpected axiom in B")

text = (B / "gnu-time.txt").read_text()
checks = [
    (r"Elapsed \(wall clock\) time \(h:mm:ss or m:ss\):\s*(\S+)", receipt["wall_time"], str),
    (r"Maximum resident set size \(kbytes\):\s*(\d+)", receipt["peak_rss_kib"], int),
    (r"Swaps:\s*(\d+)", receipt["swaps"], int),
    (r"Exit status:\s*(\d+)", receipt["exit_status"], int),
]
for pat, expected, cast in checks:
    m = re.search(pat, text)
    need(m is not None and cast(m.group(1)) == expected, f"GNU metric mismatch: {pat}")
need(receipt["swaps"] == 0, "swap reported")
need(js(B, "launch-status.json")["ssh_exit_status"] == 0, "launcher SSH failed")

limits = {"memory.high": "5368709120", "memory.max": "7516192768", "memory.swap.max": "0", "pids.max": "128"}
before, after = js(B, "host-before.json")["cgroup"], js(B, "host-after.json")["cgroup"]
for label, snap in (("before", before), ("after", after)):
    need(all(snap.get(k) == v for k,v in limits.items()), f"{label} effective cgroup caps mismatch")
    events = dict(row.split() for row in snap["memory.events"].splitlines())
    need(all(events.get(k) == "0" for k in ("high", "max", "oom", "oom_kill", "oom_group_kill")), f"{label} cgroup memory event")
need(after["memory.swap.peak"] == "0", "cgroup swap peak nonzero")
need(js(B, "host-after.json")["olean_sha256"], "green OLean checksum absent")
copy_records = sorted(B.glob("*.copy-status.json"))
need(len(copy_records) == 6, f"expected 6 copied-artifact statuses, found {len(copy_records)}")
for p in copy_records:
    need(js(B, p.name).get("exit_status") == 0, f"copy failure in {p.name}")

receipt_a = js(A, "receipt.json")
log_a = (A / "lean.log").read_text()
need(receipt_a["exit_status"] != 0, "A should be failed history")
need("Type mismatch: After simplification" in log_a and "System.Platform.numBits" in log_a, "A platform-size simplification failure missing")
need("sorryAx" in log_a, "A rejected sorryAx output missing")
need("System.Platform.numBits_eq" in source.read_text(), "B source lacks the recorded platform-width fix")

report = {
    "status": "PASS",
    "target": receipt["target"],
    "source_revision": receipt["source_revision"],
    "source_sha256": receipt["source_sha256"],
    "root_source_equals_attempt_b": True,
    "exit_status": receipt["exit_status"],
    "wall_time": receipt["wall_time"],
    "gnu_peak_rss_kib": receipt["peak_rss_kib"],
    "swaps": receipt["swaps"],
    "complete_axiom_reports": len(reports),
    "axiom_whitelist": sorted(FOUNDATIONS),
    "effective_cgroup_limits": limits,
    "cgroup_memory_peak_bytes": int(after["memory.peak"]),
    "copy_status_count": len(copy_records),
    "attempt_a": {"exit_status": receipt_a["exit_status"], "platform_size_failure": True, "sorryAx_in_failed_output": True},
    "boundary": "A generic Lean scalar/helper fragment only; this audit makes no claim about native execution closure or Rust source correspondence."
}
print(json.dumps(report, indent=2))
