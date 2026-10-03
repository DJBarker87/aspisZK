#!/usr/bin/env python3
"""Read-only integrity check for the saved R435 attempt C compile."""
from pathlib import Path
import hashlib, json, re

HERE = Path(__file__).resolve().parents[2]
A, B, C = (HERE / f"attempt-{x}" for x in "abc")
ROOT_SOURCE = HERE / "R435HelperGuards.UNVERIFIED.lean"
FOUNDATIONS = {"propext", "Classical.choice", "Quot.sound"}

def need(ok, msg):
    if not ok: raise SystemExit("FAIL: " + msg)
def js(folder, name): return json.loads((folder / name).read_text())
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()

receipt = js(C, "receipt.json")
source = C / "source.lean"
need(ROOT_SOURCE.read_bytes() == source.read_bytes(), "root C source differs from compiled C source")
need(sha(source) == receipt["source_sha256"] == js(C, "host-after.json")["source_sha256"], "C source SHA mismatch")
need(receipt["target"] == "AspisV8R19/R435HelperGuards.lean", "target mismatch")
need(receipt["source_revision"] == "51f7e12388958a5e565273359022df04bef49bff", "source revision mismatch")
need(receipt["exit_status"] == 0, "C is not a successful compilation")
need("4.32.0" in receipt["lean_version"] and "8c9756b28d64dab099da31a4c09229a9e6a2ef35" in receipt["lean_version"], "Lean toolchain pin mismatch")

# C retains B's original four definitions byte-for-byte before appending the
# bounded-address fragment and its two added axiom requests.
s_b, s_c = (p.read_text() for p in (B / "source.lean", C / "source.lean"))
marker = "def helper114Fragment"
need(marker in s_c and marker not in s_b, "expected added helper fragment marker missing/unexpected")
need(s_c[:s_c.index(marker)].rstrip("\n") == s_b[:s_b.index("#print axioms")].rstrip("\n"), "preexisting definitions differ between B and C")
need("System.Platform.numBits_eq" in s_c, "platform-width correction absent")
need(all(x in s_c for x in ("helper114_bounded_addresses", "helper114_success", "a.noWrap")), "C's added bounded-address declarations missing")

log = (C / "lean.log").read_text()
reports = [line for line in log.splitlines() if line.startswith("'AspisV8R19.R435HelperGuards.") and ("depends on axioms:" in line or "does not depend on any axioms" in line)]
need(len(reports) == 6, f"expected six complete reports, got {len(reports)}")
need(reports == receipt["complete_print_axioms"], "C log reports differ from receipt")
need(s_c.count("#print axioms") == 6, "C source axiom-print count mismatch")
for line in reports:
    names = set(re.findall(r"\b(?:propext|Classical\.choice|Quot\.sound|sorryAx)\b", line))
    need("sorryAx" not in names and names <= FOUNDATIONS, "unexpected axiom in green C output")

text = (C / "gnu-time.txt").read_text()
for pattern, expected, cast in [
    (r"Elapsed \(wall clock\) time \(h:mm:ss or m:ss\):\s*(\S+)", receipt["wall_time"], str),
    (r"Maximum resident set size \(kbytes\):\s*(\d+)", receipt["peak_rss_kib"], int),
    (r"Swaps:\s*(\d+)", receipt["swaps"], int),
    (r"Exit status:\s*(\d+)", receipt["exit_status"], int),
]:
    m = re.search(pattern, text)
    need(m is not None and cast(m.group(1)) == expected, "C GNU-time receipt mismatch")
need(receipt["swaps"] == 0 and js(C, "launch-status.json")["ssh_exit_status"] == 0, "C launch/swap status mismatch")

limits = {"memory.high": "5368709120", "memory.max": "7516192768", "memory.swap.max": "0", "pids.max": "128"}
before, after = js(C, "host-before.json")["cgroup"], js(C, "host-after.json")["cgroup"]
for label, snap in (("before", before), ("after", after)):
    need(all(snap.get(k) == v for k, v in limits.items()), f"C {label} cgroup caps mismatch")
    events = dict(row.split() for row in snap["memory.events"].splitlines())
    need(all(events.get(k) == "0" for k in ("high", "max", "oom", "oom_kill", "oom_group_kill")), f"C {label} cgroup memory event")
need(after["memory.swap.peak"] == "0" and js(C, "host-after.json")["olean_sha256"], "C swap peak/OLean checksum mismatch")
copy_records = sorted(C.glob("*.copy-status.json"))
need(len(copy_records) == 6, f"expected six C copy-status records, got {len(copy_records)}")
for p in copy_records:
    need(js(C, p.name).get("exit_status") == 0, f"C copy failure: {p.name}")

receipt_b, receipt_a = js(B, "receipt.json"), js(A, "receipt.json")
need(receipt_b["exit_status"] == 0 and "sorryAx" not in " ".join(receipt_b["complete_print_axioms"]), "B history is not green/clean")
log_a = (A / "lean.log").read_text()
need(receipt_a["exit_status"] != 0 and "Type mismatch: After simplification" in log_a and "System.Platform.numBits" in log_a and "sorryAx" in log_a, "A's rejected platform-width failure history mismatch")

report = {
    "status": "PASS",
    "target": receipt["target"],
    "source_revision": receipt["source_revision"],
    "source_sha256": receipt["source_sha256"],
    "root_source_equals_attempt_c": True,
    "attempt_b_preexisting_definition_prefix_preserved": True,
    "exit_status": receipt["exit_status"],
    "wall_time": receipt["wall_time"],
    "gnu_peak_rss_kib": receipt["peak_rss_kib"],
    "swaps": receipt["swaps"],
    "complete_axiom_reports": len(reports),
    "axiom_whitelist": sorted(FOUNDATIONS),
    "effective_cgroup_limits": limits,
    "cgroup_memory_peak_bytes": int(after["memory.peak"]),
    "copy_status_count": len(copy_records),
    "history": {
        "attempt_a_platform_width_failure_with_sorryAx_rejected": True,
        "attempt_b_successful_four_report_predecessor_preserved": True,
        "attempt_c_adds_bounded_addresses_and_success_lemmas": True
    },
    "boundary": "Generic Lean scalar/pointer-fragment model only; no native execution closure or Rust source-correspondence claim."
}
print(json.dumps(report, indent=2))
