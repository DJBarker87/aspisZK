#!/usr/bin/env python3
"""Read-only R434 command-scope and saved-result audit against R431."""
from pathlib import Path
import hashlib, json, re

HERE = Path(__file__).resolve().parents[1]
R431 = HERE.parents[1] / "r431-actual-slice-construction" / "root-launch-a"
SAVED = HERE / "saved-output"
RECEIPT = json.loads((HERE / "changed-scope-receipt.json").read_text())

def need(condition, message):
    if not condition:
        raise SystemExit("FAIL: " + message)
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def js(path): return json.loads(path.read_text())

r431_scope = js(R431 / "changed-scope-receipt.json")
r431_command = js(R431 / "saved-output" / "extract-command.json")["command"]
r431_after = js(R431 / "saved-output" / "host-reservation-after.json")
cmd = js(SAVED / "extract-command.json")
result = js(SAVED / "result.json")
before = js(SAVED / "host-reservation-before.json")
after = js(SAVED / "host-reservation-after.json")

# The selected command starts exactly from R431's command and adds only the two
# helper includes plus the fresh destination. Keep argument ordering exact.
base = RECEIPT["base_command"]
new = RECEIPT["new_command"]
need(base == r431_command, "R434 base command is not byte-for-byte R431 command")
need(RECEIPT["permitted_changes"] == ["two narrowly scoped helper includes", "fresh output path"], "scope receipt allowed-change declaration differs")
base_dest = base.index("--dest-file")
new_dest = new.index("--dest-file")
need(new[:base_dest] == base[:base_dest], "R434 changed command prefix before helper includes")
need(new[base_dest:new_dest] == [
    "--include", "core::ptr::const_ptr::_::offset_from_unsigned::precondition_check",
    "--include", "core::num::_::unchecked_add::precondition_check",
], "R434 command delta is not exactly the two helper includes")
need(new[new_dest] == "--dest-file" and new[new_dest+1] != base[base_dest+1], "fresh destination delta absent")
need(new[new_dest+2:] == base[base_dest+2:], "R434 changed command arguments after destination")
need(cmd["command"] == new, "saved actual extraction command differs from reviewed scope command")
need(cmd["start_from"] == ["crate::freeze"] and cmd["monomorphize"] is True, "root or monomorphize changed")
need(cmd["include"] == [new[i+1] for i, x in enumerate(new) if x == "--include"], "saved include list differs from command")
need("--print-original-ullbc" not in new, "unexpected raw MIR flag")
need(RECEIPT["remote_script_sha256"] == sha(HERE / "remote.py"), "remote script hash mismatch")
need(js(HERE / "launch-status.json")["remote_script_sha256"] == sha(HERE / "remote.py"), "launch receipt script hash mismatch")
launch_status = js(HERE / "launch-status.json")
collection_status = js(HERE / "collection-status.json")
need(launch_status["ssh_exit_status"] == 0 and launch_status["launch_revision"] == RECEIPT["revision"], "launch status/revision mismatch")
need(collection_status["exit_status"] == 0 and collection_status["tar_bytes"] > 0, "saved-output collection failed")
need(RECEIPT["revision"] == "f997fffc34b60ebf9a93e80b8edbdc96485ae9d6", "campaign revision mismatch")

# Check source, compiler, Rust toolchain and baseline pins recorded at launch and end.
sources_before = before["source_hashes_before"]
sources_after = after["source_hashes_after"]
need(sources_before == sources_after and len(sources_before) == 8, "selected Rust/Cargo source hashes changed or incomplete")
need(sources_before == r431_after["source_hashes_after"], "R434 selected source hashes differ from R431 terminal snapshot")
need(result["source_hashes_before_after"]["before"] == sources_before and result["source_hashes_before_after"]["after"] == sources_after, "result source hash receipt mismatch")
need(result["baseline_sha256_before_after"] == ["e8ee00cd440f7594e1a163290219c4e64a24141a722da6a861a45d0e61757e31"] * 2, "R185 baseline pin changed")
need(result["source_commit"] == "cb50ff16b9f1066b8a97dc06da704de2da2fa41c", "Charon source commit mismatch")
need(result["original_driver_sha256"] == "4cb603ad51132f298a63a9c2a8cc8c629c73edeff22516fbf56ba5decee70938", "Charon driver hash mismatch")
need(result["charon_toolchain"] == "nightly-2026-06-01", "Charon toolchain pin mismatch")
need("commit-hash: 14210df0e27ccd7d9e6a05b8085cbd438e4bbc65" in result["rustc_version_verbose"], "rustc commit mismatch")
need(result["requested_root"] == "crate::freeze" and result["has_errors"] is False, "root or LLBC error flag mismatch")
need(result["formal_axioms"] == "N/A; diagnostic LLBC only", "formal axioms field mismatch")
need(result["base_extract_command_sha256"] == "2bd178956b2fc4aaed055bc899349046f8969b238fa85bf027dd861becb2db96", "base extract-command pin mismatch")
need(cmd["baseline_sha256"] == result["baseline_sha256_before_after"][0], "command record baseline mismatch")
need(cmd["source_hashes"] == sources_before, "command source hashes mismatch")

# Saved logs and output integrity plus GNU metrics. Cgroup peak is recorded
# separately from GNU time; the two measurements need not be equal.
llbc = SAVED / "R434ActualFoldUbHelpers.llbc"
need(llbc.is_file() and sha(llbc) == result["llbc_sha256"], "LLBC checksum mismatch")
need(result["llbc_exists"] is True, "LLBC absent per receipt")
for name, field in (("charon.stdout.log", "charon_stdout_sha256"), ("charon.stderr.log", "charon_stderr_sha256")):
    p = SAVED / name
    need(sha(p) == result[field], f"{name} hash mismatch")
    need(p.stat().st_size == result[field.replace("sha256", "bytes")], f"{name} size mismatch")
gnu = (SAVED / "gnu-time.txt").read_text()
patterns = {
    "wall_time": r"Elapsed \(wall clock\) time \(h:mm:ss or m:ss\):\s*(\S+)",
    "peak_rss_kib": r"Maximum resident set size \(kbytes\):\s*(\d+)",
    "swap_count": r"Swaps:\s*(\d+)",
    "gnu_time_exit_status": r"Exit status:\s*(\d+)",
}
for key, pattern in patterns.items():
    match = re.search(pattern, gnu)
    need(match is not None, f"GNU metric {key} absent")
    actual = int(match.group(1)) if key != "wall_time" else match.group(1)
    need(actual == result[key], f"GNU metric {key} differs from receipt")
need(result["charon_exit_status"] == result["gnu_time_exit_status"] == 0, "extraction/gnu-time exit mismatch")
need(result["swap_count"] == 0, "swap occurred")

limits = {"memory.high": "5368709120", "memory.max": "7516192768", "memory.swap.max": "0", "pids.max": "128"}
for label, snap in (("preflight", before["effective_cgroup_before"]), ("terminal", after["effective_cgroup_after"])):
    need(all(snap.get(k) == v for k, v in limits.items()), f"{label} effective cgroup cap mismatch")
    events = dict(line.split() for line in snap["memory.events"].splitlines())
    need(all(events.get(k) == "0" for k in ("high", "max", "oom", "oom_kill", "oom_group_kill")), f"{label} cgroup memory event")
need(after["effective_cgroup_after"]["memory.swap.peak"] == "0", "effective cgroup swap peak nonzero")
need(before["candidate_memory_max_bytes"] == 7 * 1024**3, "reservation cap mismatch")
need(before["system_reserved_memory_max_bytes"] == 128 * 1024**2, "system reservation record mismatch")
need(before["candidate_memory_max_bytes"] + before["active_slice_memory_max_bytes"] + before["system_reserved_memory_max_bytes"] <= before["safe_working_limit_bytes"], "recorded host reservation exceeds safe limit")
memavail = int(before["host_meminfo_before"]["MemAvailable"].split()[0]) * 1024
need(memavail - before["candidate_memory_max_bytes"] >= 24 * 1024**3, "recorded available-memory margin insufficient")

report = {
    "status": "PASS",
    "scope": "R434 command equals R431 command plus exactly two helper includes and a fresh destination",
    "R431_base_command_exact": True,
    "source_hashes_match_R431_terminal_snapshot": True,
    "added_includes": ["core::ptr::const_ptr::_::offset_from_unsigned::precondition_check", "core::num::_::unchecked_add::precondition_check"],
    "launch_revision": RECEIPT["revision"],
    "launch_and_collection_exit_status": [launch_status["ssh_exit_status"], collection_status["exit_status"]],
    "result": {k: result[k] for k in ("charon_exit_status", "wall_time", "peak_rss_kib", "swap_count", "llbc_sha256", "has_errors", "formal_axioms")},
    "source_hash_count_unchanged": len(sources_before),
    "pinned_charon_commit": result["source_commit"],
    "pinned_rustc": "14210df0e27ccd7d9e6a05b8085cbd438e4bbc65",
    "effective_caps": limits,
    "reservation_max_bytes": before["candidate_memory_max_bytes"],
    "terminal_cgroup_peak_bytes": int(after["effective_cgroup_after"]["memory.peak"]),
    "GNU_RSS_and_cgroup_peak_reported_separately": True,
    "boundary": "Diagnostic LLBC extraction only; no formal axioms apply, and no source-semantics or pointer-UB theorem is asserted by this audit."
}
print(json.dumps(report, indent=2))
