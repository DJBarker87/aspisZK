from pathlib import Path
import hashlib,json,os,re,signal,subprocess,sys,time
W=Path(__file__).resolve().parent; cfg=json.loads((W/"attempt-config.json").read_text()); sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert subprocess.run([sys.executable,str(W/"check_sourcecut.py")]).returncode==0
assert subprocess.run([sys.executable,str(W/"check_llbc.py")]).returncode==0
llbc=W/"runs-charon/helper-projection.llbc"; assert llbc.exists()
d=json.loads(llbc.read_text()); assert not d.get("has_errors"); t=d["translated"]
required={
 "pub fn mul(self, rhs: QM31) -> QM31":("QM31.mul",935),
 "pub fn mul(self, rhs: CM31) -> CM31":("CM31.mul",306),
 "pub fn add(self, rhs: CM31) -> CM31":("CM31.add",281),
 "pub fn sub(self, rhs: CM31) -> CM31":("CM31.sub",289),
 "pub fn add(self, rhs: M31) -> M31":("M31.add",62),
 "pub fn sub(self, rhs: M31) -> M31":("M31.sub",94),
 "pub fn mul(self, rhs: M31) -> M31":("M31.mul",133),
 "fn reduce_u64(x: u64) -> u32":("reduce_u64",31),
 "fn mul_by_r(x: CM31) -> CM31":("mul_by_r",860),
}
found={}
for f in t["fun_decls"]:
 m=f.get("item_meta") or {}; txt=m.get("source_text") or ""; sp=m.get("span",{}).get("data",{}); beg=(sp.get("beg") or {}).get("line"); fid=sp.get("file_id")
 for needle,(label,line) in required.items():
  if needle in txt and beg==line: found[label]=(m.get("opacity"),fid,beg)
assert set(found)=={v[0] for v in required.values()},(found,required)
assert all(v[0]=="Transparent" for v in found.values()),found
assert sha(Path(cfg["aeneas_path"]))==cfg["aeneas_sha256"]
cgline=Path("/proc/self/cgroup").read_text().strip(); assert cgline.startswith("0::"),cgline
cg=Path("/sys/fs/cgroup")/cgline[3:].lstrip("/"); limits={k:(cg/k).read_text().strip() for k in ("memory.high","memory.max","memory.swap.max")}
assert limits=={"memory.high":str(cfg["scope_memory_high_bytes"]),"memory.max":str(cfg["scope_memory_max_bytes"]),"memory.swap.max":"0"},limits
run=W/"runs-aeneas"; run.mkdir(exist_ok=False); gen=run/"generated"; a=Path(cfg["aeneas_path"])
argv=[str(a),"-sequential","-no-progress-bar","-abort-on-error","-backend","lean","-namespace","AspisR1S9ActualWideMulCutV1","-dest",str(gen),"-subdir","AspisR1S9ActualWideMulCutV1","-split-files","-emit-json",str(llbc)]
env=os.environ.copy(); env.update({"PATH":"/home/dombarker/.cargo/bin:/usr/bin:/bin"})
for k in ("RUSTFLAGS","RUSTC_WRAPPER","RUSTC_WORKSPACE_WRAPPER","CARGO_ENCODED_RUSTFLAGS"): env.pop(k,None)
command={"phase":"aeneas","argv":argv,"cwd":str(W),"limits":limits,"cgroup":str(cg),"llbc_sha256":sha(llbc),"tool_pins":{str(a):cfg["aeneas_sha256"]},"transparent_target_declarations":found}
(run/"command.json").write_text(json.dumps(command,indent=2)+"\n"); (run/"environment.json").write_text(json.dumps({"PATH":env["PATH"]},indent=2)+"\n")
before=(cg/"memory.events").read_text(); start=time.monotonic(); timed=False
with (run/"stdout.log").open("x") as out:
 proc=subprocess.Popen(["/usr/bin/time","-v","-o",str(run/"time.log"),*argv],cwd=W,env=env,stdout=out,stderr=subprocess.STDOUT,start_new_session=True)
 while proc.poll() is None:
  if time.monotonic()-start>600:
   timed=True; os.killpg(proc.pid,signal.SIGTERM)
   try: proc.wait(timeout=3)
   except subprocess.TimeoutExpired: os.killpg(proc.pid,signal.SIGKILL); proc.wait()
   break
  time.sleep(.1)
status=proc.returncode; receipt={**command,"exit_status":status,"timed_out":timed,"wall_seconds":round(time.monotonic()-start,3),"swap_current_bytes":int((cg/"memory.swap.current").read_text()),"memory_peak_bytes":int((cg/"memory.peak").read_text()),"memory_events_before":before,"memory_events_after":(cg/"memory.events").read_text(),"finished_utc":time.strftime("%Y-%m-%dT%H:%M:%SZ",time.gmtime())}
txt=(run/"time.log").read_text(); m=re.search(r"Maximum resident set size \(kbytes\): (\d+)",txt); receipt["max_process_rss_kib"]=int(m.group(1)) if m else None
if (gen/"translation.json").exists(): receipt["translation_sha256"]=sha(gen/"translation.json")
receipt["generated_lean"]={str(p.relative_to(run)):sha(p) for p in sorted(gen.rglob("*.lean"))} if gen.exists() else {}
(run/"receipt.json").write_text(json.dumps(receipt,indent=2)+"\n"); print(json.dumps(receipt,indent=2))
if status == 0:
 meta=json.loads((gen/"translation.json").read_text())
 required=("focused_wide_exact_mul", "field.wide_exact.WideExact.mul", "field.QM31.mul", "field.CM31.mul", "field.M31.mul")
 names=[x.get("lean_name","") for x in meta.get("functions",[])]
 assert meta.get("functions") and meta.get("types"), "Aeneas emitted an empty translation"
 assert all(any(n.endswith(x) for n in names) for x in required), (required,names)
receipt["translation_nonempty_assertion"] = bool(status == 0 and (gen/"translation.json").exists() and json.loads((gen/"translation.json").read_text()).get("functions") and json.loads((gen/"translation.json").read_text()).get("types"))
sys.exit(status if status is not None else 1)
