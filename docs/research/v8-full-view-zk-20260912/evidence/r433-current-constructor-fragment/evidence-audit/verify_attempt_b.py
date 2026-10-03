#!/usr/bin/env python3
"""Read-only integrity check for the saved R433 attempt B compile."""
from pathlib import Path
import hashlib, json, re

HERE = Path(__file__).resolve().parent.parent
ATT = HERE / "attempt-b"
ATT_A = HERE / "attempt-a"
ROOT_SOURCE = HERE / "R433ConstructorFragment.UNVERIFIED.lean"
FOUNDATIONS = {"propext", "Classical.choice", "Quot.sound"}

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()
def read_json(name, attempt=ATT):
    return json.loads((attempt / name).read_text())
def require(ok, why):
    if not ok:
        raise SystemExit("FAIL: " + why)

receipt = read_json("receipt.json")
source = ATT / "source.lean"
require(ROOT_SOURCE.read_bytes() == source.read_bytes(), "root source differs from compiled B source")
require(sha(source) == receipt["source_sha256"], "B source hash differs from receipt")
require(read_json("host-after.json")["source_sha256"] == receipt["source_sha256"], "host-after source hash mismatch")
require(receipt["target"] == "AspisV8R19/R433ConstructorFragment.lean", "unexpected target")
require(receipt["source_revision"] == "7eb0fa2e7cc429a027e5e19f8460ccd22d162ea0", "source revision mismatch")
require(receipt["exit_status"] == 0, "receipt is not green")
require(receipt["lean_version"].startswith("Lean (version 4.32.0,") and "8c9756b28d64dab099da31a4c09229a9e6a2ef35" in receipt["lean_version"], "Lean pin mismatch")

# Cross-check compiler output with complete receipt report and source print requests.
log = (ATT / "lean.log").read_text()
printed = [line for line in log.splitlines() if line.startswith("'AspisV8R19.R433ConstructorFragment.") and ("does not depend on any axioms" in line or "depends on axioms:" in line)]
require(len(printed) == 4, f"expected 4 axiom report lines, found {len(printed)}")
require(printed == receipt["complete_print_axioms"], "complete axiom output differs from receipt")
require(source.read_text().count("#print axioms") == 4, "source axiom-request count mismatch")
for line in printed:
    names = set(re.findall(r"\b(?:propext|Classical\.choice|Quot\.sound|sorryAx)\b", line))
    require("sorryAx" not in names, "green output contains sorryAx")
    require(names <= FOUNDATIONS, "non-foundational axiom in green output")

# GNU time fields are independent from the cgroup's own peak measurement.
gnu = (ATT / "gnu-time.txt").read_text()
wall = re.search(r"Elapsed \(wall clock\) time \(h:mm:ss or m:ss\):\s*(\S+)", gnu)
rss = re.search(r"Maximum resident set size \(kbytes\):\s*(\d+)", gnu)
swaps = re.search(r"Swaps:\s*(\d+)", gnu)
exit_status = re.search(r"Exit status:\s*(\d+)", gnu)
require(wall and wall.group(1) == receipt["wall_time"], "GNU wall time differs from receipt")
require(rss and int(rss.group(1)) == receipt["peak_rss_kib"], "GNU RSS differs from receipt")
require(swaps and int(swaps.group(1)) == receipt["swaps"] == 0, "swap metric mismatch")
require(exit_status and int(exit_status.group(1)) == receipt["exit_status"], "GNU exit differs from receipt")

before, after = read_json("host-before.json"), read_json("host-after.json")
expected = {"memory.high": "5368709120", "memory.max": "7516192768", "memory.swap.max": "0", "pids.max": "128"}
for label, snap in (("before", before["cgroup"]), ("after", after["cgroup"])):
    require(all(snap[k] == v for k, v in expected.items()), f"{label} effective cgroup limits mismatch")
    events = dict(line.split() for line in snap["memory.events"].splitlines())
    require(all(events.get(k) == "0" for k in ("high", "max", "oom", "oom_kill", "oom_group_kill")), f"{label} cgroup memory event")
require(after["olean_sha256"], "successful OLean hash absent")

launch = read_json("launch-status.json")
require(launch["ssh_exit_status"] == 0, "SSH launcher failed")
copy_files = sorted(ATT.glob("*.copy-status.json"))
require(len(copy_files) == 6, f"expected 6 copy status records, got {len(copy_files)}")
for path in copy_files:
    obj = json.loads(path.read_text())
    require(obj.get("exit_status") == 0, f"artifact copy failed: {path.name}")

# Preserve and characterize attempt A without treating its sorryAx output as evidence.
receipt_a = read_json("receipt.json", ATT_A)
log_a = (ATT_A / "lean.log").read_text()
require(receipt_a["exit_status"] != 0, "attempt A unexpectedly not a failure")
require("fail to show termination" in log_a and "evalProgram" in log_a, "attempt A termination diagnostic missing")
require("sorryAx" in log_a, "attempt A rejected axiom history missing")

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
    "complete_axiom_reports": len(printed),
    "axiom_whitelist": sorted(FOUNDATIONS),
    "effective_cgroup_limits": expected,
    "cgroup_memory_peak_bytes": int(after["cgroup"]["memory.peak"]),
    "copy_status_count": len(copy_files),
    "attempt_a": {"exit_status": receipt_a["exit_status"], "termination_diagnostic": True, "sorryAx_in_failed_output": True},
    "boundary": "Lean model of a generic pointer/constructor fragment only; no Rust source correspondence, lifetime, aliasing, or whole-callback theorem is established by this custody audit."
}
print(json.dumps(report, indent=2))
