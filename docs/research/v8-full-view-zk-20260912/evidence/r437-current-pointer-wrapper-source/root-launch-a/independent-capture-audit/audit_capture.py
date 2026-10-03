#!/usr/bin/env python3
"""Read-only R437 command-scope and saved-capture audit against R434."""
from pathlib import Path
import hashlib, json, re

HERE = Path(__file__).resolve().parents[1]
R434 = HERE.parents[1] / "r434-actual-fold-control" / "root-launch-a"
SAVED = HERE / "saved-output"
SCOPE = json.loads((HERE / "changed-scope-receipt.json").read_text())
def need(ok,msg):
    if not ok: raise SystemExit("FAIL: "+msg)
def js(d,n=None): return json.loads((d/n if n else d).read_text())
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()

base = SCOPE["base_command"]
new = SCOPE["new_command"]
r434_command = json.loads((R434/"saved-output"/"extract-command.json").read_text())["command"]
cmd = js(SAVED/"extract-command.json")
result = js(SAVED/"result.json")
before = js(SAVED/"host-reservation-before.json")
after = js(SAVED/"host-reservation-after.json")
need(base == r434_command, "R437 base command differs from R434 actual command")
need(SCOPE["permitted_changes"] == ["two narrowly scoped type includes", "fresh output path"], "scope declaration mismatch")
base_dest, new_dest = base.index("--dest-file"), new.index("--dest-file")
need(new[:base_dest] == base[:base_dest], "arguments before includes changed")
need(new[base_dest:new_dest] == [
 "--include","core::ptr::non_null::NonNull",
 "--include","core::marker::PhantomData",
], "command delta is not exactly NonNull and PhantomData includes")
need(new[new_dest+2:] == base[base_dest+2:] and new[new_dest+1] != base[base_dest+1], "destination/following arguments mismatch")
need(cmd["command"] == new, "saved extraction command mismatch")
need(cmd["start_from"] == ["crate::freeze"] and cmd["monomorphize"] is True, "root or monomorphize changed")
need(cmd["include"] == [new[i+1] for i,x in enumerate(new) if x=="--include"], "saved include list mismatch")
need("--print-original-ullbc" not in new, "unexpected MIR output flag")
need(SCOPE["revision"] == "77857d6028d1b4016949aa14b19c17282e2cec0c", "campaign revision mismatch")
need(SCOPE["remote_script_sha256"] == sha(HERE/"remote.py"), "remote.py checksum mismatch")
need(js(HERE,"launch-status.json")["remote_script_sha256"] == sha(HERE/"remote.py"), "launch receipt script hash mismatch")
launch_status=js(HERE,"launch-status.json")
collection=js(HERE,"collection-status.json")
need(launch_status["ssh_exit_status"]==0 and launch_status["launch_revision"]==SCOPE["revision"], "launch failed/revision mismatch")
need(collection["exit_status"]==0 and collection["tar_bytes"]>0, "output collection failed")

src_before=before["source_hashes_before"]
src_after=after["source_hashes_after"]
need(src_before==src_after and len(src_before)==8, "selected sources changed or incomplete")
r434_after=js(R434/"saved-output"/"host-reservation-after.json")
need(src_before==r434_after["source_hashes_after"], "R437 source hashes differ from R434 terminal snapshot")
need(result["source_hashes_before_after"]=={"before":src_before,"after":src_after}, "result source hash receipt mismatch")
need(result["baseline_sha256_before_after"]==["e8ee00cd440f7594e1a163290219c4e64a24141a722da6a861a45d0e61757e31"]*2, "baseline mismatch")
need(result["source_commit"]=="cb50ff16b9f1066b8a97dc06da704de2da2fa41c", "Charon source commit mismatch")
need(result["original_driver_sha256"]=="4cb603ad51132f298a63a9c2a8cc8c629c73edeff22516fbf56ba5decee70938", "driver hash mismatch")
need(result["charon_toolchain"]=="nightly-2026-06-01" and "commit-hash: 14210df0e27ccd7d9e6a05b8085cbd438e4bbc65" in result["rustc_version_verbose"], "toolchain pin mismatch")
need(result["requested_root"]=="crate::freeze" and result["has_errors"] is False, "root or error flag mismatch")
need(result["formal_axioms"]=="N/A; diagnostic LLBC only", "formal axioms field mismatch")
need(result["base_extract_command_sha256"]=="2bd178956b2fc4aaed055bc899349046f8969b238fa85bf027dd861becb2db96", "extract-command baseline hash mismatch")
need(cmd["source_hashes"]==src_before and cmd["baseline_sha256"]==result["baseline_sha256_before_after"][0], "command hash pins mismatch")

llbc=SAVED/"R437PointerWrapperLayout.llbc"
need(result["llbc_exists"] is True and sha(llbc)==result["llbc_sha256"]=="bafe9c1297a8ea92eaea3c37c685da3f5d3fe2e04c335ac9f1f4d64c4312386c", "LLBC hash mismatch")
for name,key in (("charon.stdout.log","charon_stdout_sha256"),("charon.stderr.log","charon_stderr_sha256")):
 p=SAVED/name; need(sha(p)==result[key],f"{name} hash mismatch")
 sizekey=key.replace("sha256","bytes");need(p.stat().st_size==result[sizekey],f"{name} length mismatch")
gnu=(SAVED/"gnu-time.txt").read_text()
for pattern,expected,cast in [
 (r"Elapsed \(wall clock\) time \(h:mm:ss or m:ss\):\s*(\S+)",result["wall_time"],str),
 (r"Maximum resident set size \(kbytes\):\s*(\d+)",result["peak_rss_kib"],int),
 (r"Swaps:\s*(\d+)",result["swap_count"],int),
 (r"Exit status:\s*(\d+)",result["gnu_time_exit_status"],int)]:
 m=re.search(pattern,gnu);need(m is not None and cast(m.group(1))==expected,"GNU time metric mismatch")
need(result["charon_exit_status"]==result["gnu_time_exit_status"]==0 and result["swap_count"]==0,"run exit/swap mismatch")
limits={"memory.high":"5368709120","memory.max":"7516192768","memory.swap.max":"0","pids.max":"128"}
for label,snap in (("before",before["effective_cgroup_before"]),("terminal",after["effective_cgroup_after"])):
 need(all(snap.get(k)==v for k,v in limits.items()),f"{label} effective cgroup limits mismatch")
 ev=dict(line.split() for line in snap["memory.events"].splitlines())
 need(all(ev.get(k)=="0" for k in ("high","max","oom","oom_kill","oom_group_kill")),f"{label} cgroup memory event")
need(after["effective_cgroup_after"]["memory.swap.peak"]=="0","cgroup swap peak nonzero")
need(before["candidate_memory_max_bytes"]+before["active_slice_memory_max_bytes"]+before["system_reserved_memory_max_bytes"]<=before["safe_working_limit_bytes"],"prelaunch host reservation exceeds safe limit")
memavail=int(before["host_meminfo_before"]["MemAvailable"].split()[0])*1024
need(memavail-before["candidate_memory_max_bytes"]>=24*1024**3,"prelaunch available-memory margin insufficient")

report={
 "status":"PASS",
 "scope":"R437 command equals R434 command plus exactly NonNull and PhantomData includes and fresh destination",
 "added_includes":["core::ptr::non_null::NonNull","core::marker::PhantomData"],
 "launch_revision":SCOPE["revision"],
 "launch_collection_status":[launch_status["ssh_exit_status"],collection["exit_status"]],
 "run":{"exit_status":result["charon_exit_status"],"wall_time":result["wall_time"],"gnu_peak_rss_kib":result["peak_rss_kib"],"swaps":result["swap_count"],"llbc_sha256":result["llbc_sha256"],"has_errors":result["has_errors"],"formal_axioms":result["formal_axioms"]},
 "source_hashes_unchanged_count":len(src_before),
 "pinned_charon_commit":result["source_commit"],
 "pinned_rustc_commit":"14210df0e27ccd7d9e6a05b8085cbd438e4bbc65",
 "effective_caps":limits,
 "reservation_max_bytes":before["candidate_memory_max_bytes"],
 "terminal_cgroup_peak_bytes":int(after["effective_cgroup_after"]["memory.peak"]),
 "gnu_rss_and_cgroup_peak_recorded_separately":True,
 "boundary":"Diagnostic LLBC only. No formal axiom or pointer-layout/source-semantics theorem is established by this audit."
}
print(json.dumps(report,indent=2))
