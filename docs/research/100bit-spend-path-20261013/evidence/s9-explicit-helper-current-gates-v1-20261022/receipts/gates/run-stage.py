from pathlib import Path
import hashlib, json, os, re, signal, subprocess, sys, time

W=Path(__file__).resolve().parent
RUN=W.parent
phase=sys.argv[1]
assert phase in {"native","sbf"}
src=RUN/"work/src"
manifest=src/"s9-candidate-source-manifest.json"
doc=json.loads(manifest.read_text())
expected_files=doc["files"]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
actual={rel:sha(src/rel) for rel in expected_files}
assert actual==expected_files, {p:{"expected":expected_files[p],"actual":actual[p]} for p in expected_files if expected_files[p]!=actual[p]}
manifest_sha=sha(manifest)
G=1024**3
cgline=Path("/proc/self/cgroup").read_text().strip(); assert cgline.startswith("0::"),cgline
cg=Path("/sys/fs/cgroup")/cgline[3:].lstrip("/")
limits={k:(cg/k).read_text().strip() for k in ("memory.high","memory.max","memory.swap.max")}
assert limits=={"memory.high":str(10*G),"memory.max":str(12*G),"memory.swap.max":"0"},limits
logdir=RUN/"gates"/phase
logdir.mkdir(parents=True,exist_ok=False)
env=os.environ.copy()
env.update({"CARGO_NET_OFFLINE":"true","CARGO_BUILD_JOBS":"4"})
for k in ("RUSTFLAGS","CARGO_ENCODED_RUSTFLAGS","ASPIS_R1_POOL_PROGRAM_ID","ASPIS_R1_REGISTRY_PROGRAM_ID"):
 env.pop(k,None)
if phase=="native":
 env.update({"CARGO_TARGET_DIR":"/home/dombarker/project-offloads/s4-three-source-review-20261022/run1/work/native-target"})
 argv=["/home/dombarker/.cargo/bin/cargo","test","--release","--offline","--locked","-j4","-p","aspis-r1-cost-probe"]
 expected_time="incremental optimized crate compile if fingerprints change, then native tests"
else:
 env.update({"CARGO_TARGET_DIR":"/home/dombarker/project-offloads/s4-three-source-review-20261022/run1/work/sbf-target-verifier",
             "CARGO_TARGET_SBPF_SOLANA_SOLANA_RUSTFLAGS":"-C link-arg=--threads=4"})
 argv=["/home/dombarker/.local/share/solana/install/releases/3.1.13/solana-release/bin/cargo-build-sbf",
       "--manifest-path",str(src/"programs/r1-cost-probe/Cargo.toml"),
       "--sbf-out-dir",str(RUN/"artifacts"),"--features","pool-adapter,private-leaf-salts",
       "--skip-tools-install","--offline","-j","4","--","--locked"]
 expected_time="optimized incremental SBF compile/link for changed weights.rs; no fixture simulation"
for k in ("CARGO_TARGET_DIR","CARGO_TARGET_SBPF_SOLANA_SOLANA_RUSTFLAGS"):
 if k in env: pass
cmd=["/usr/bin/time","-v","-o",str(logdir/"time.log"),*argv]
receipt={"phase":phase,"cwd":str(src),"argv":argv,"research_head":doc["research_head"],
         "candidate_weights_sha256":doc["candidate_weights_sha256"],"source_manifest_sha256":manifest_sha,
         "admitted_source_file_count":len(actual),"admitted_source_hashes":actual,
         "limits":limits,"cgroup":str(cg),"expected_time":expected_time,
         "target_dir":env["CARGO_TARGET_DIR"],"started_utc":time.strftime("%Y-%m-%dT%H:%M:%SZ",time.gmtime())}
(logdir/"command.json").write_text(json.dumps({**receipt,"env":{k:env.get(k) for k in ("CARGO_NET_OFFLINE","CARGO_TARGET_DIR","CARGO_TARGET_SBPF_SOLANA_SOLANA_RUSTFLAGS","CARGO_BUILD_JOBS")}},indent=2)+"\n")
before=(cg/"memory.events").read_text(); start=time.monotonic(); watchdog=None
with (logdir/"stdout-stderr.log").open("x") as out:
 p=subprocess.Popen(cmd,cwd=src,env=env,stdout=out,stderr=subprocess.STDOUT,start_new_session=True)
 while p.poll() is None:
  if time.monotonic()-start>600:
   watchdog="timeout_600s"; os.killpg(p.pid,signal.SIGTERM)
   try:p.wait(timeout=5)
   except subprocess.TimeoutExpired:os.killpg(p.pid,signal.SIGKILL)
   break
  time.sleep(.1)
 status=p.wait()
timing=(logdir/"time.log").read_text()
rss=re.search(r"Maximum resident set size \(kbytes\):\s*(\d+)",timing)
receipt.update({"exit_status":status,"wall_seconds":round(time.monotonic()-start,3),
                "peak_process_rss_kib":int(rss[1]) if rss else None,
                "scope_memory_peak_bytes":int((cg/"memory.peak").read_text()),
                "scope_swap_current_bytes_at_exit":int((cg/"memory.swap.current").read_text()),
                "memory_events_before":before,"memory_events_after":(cg/"memory.events").read_text(),
                "watchdog":watchdog,"finished_utc":time.strftime("%Y-%m-%dT%H:%M:%SZ",time.gmtime())})
if phase=="sbf" and status==0:
 artifact=RUN/"artifacts/aspis_r1_cost_probe_program.so"
 assert artifact.is_file(), "SBF command exited zero but artifact is missing"
 receipt["candidate_artifact_sha256"]=sha(artifact)
 receipt["candidate_artifact_bytes"]=artifact.stat().st_size
(logdir/"receipt.json").write_text(json.dumps(receipt,indent=2)+"\n")
print(json.dumps(receipt),flush=True)
raise SystemExit(status)
