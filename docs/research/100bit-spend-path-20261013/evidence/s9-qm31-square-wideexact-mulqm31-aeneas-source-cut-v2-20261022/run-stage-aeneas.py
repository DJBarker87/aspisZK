from pathlib import Path
import hashlib,json,os,re,signal,subprocess,sys,time
W=Path(__file__).resolve().parent
cfg=json.loads((W/"attempt-config.json").read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert subprocess.run([sys.executable,str(W/"check_sourcecut.py")]).returncode==0
assert subprocess.run([sys.executable,str(W/"check_llbc.py")]).returncode==0
llbc=W/"runs-charon/helper-projection.llbc"
assert llbc.exists() and sha(llbc)==cfg["expected_llbc_sha256"]
d=json.loads(llbc.read_text()); assert not d.get("has_errors",True)
a=Path(cfg["aeneas_path"]); assert sha(a)==cfg["aeneas_sha256"]
cgline=Path("/proc/self/cgroup").read_text().strip(); assert cgline.startswith("0::"),cgline
cg=Path("/sys/fs/cgroup")/cgline[3:].lstrip("/")
limits={k:(cg/k).read_text().strip() for k in ("memory.high","memory.max","memory.swap.max")}
want={"memory.high":str(cfg["scope_memory_high_bytes"]),"memory.max":str(cfg["scope_memory_max_bytes"]),"memory.swap.max":"0"}
assert limits==want,(limits,want)
run=W/"runs-aeneas"; run.mkdir(exist_ok=False); gen=run/"generated"
ns=cfg["aeneas_namespace"]
argv=[str(a),"-sequential","-no-progress-bar","-abort-on-error","-backend","lean","-namespace",ns,"-dest",str(gen),"-subdir",ns,"-split-files","-emit-json",str(llbc)]
env=os.environ.copy(); env.update({"PATH":"/home/dombarker/.cargo/bin:/usr/bin:/bin"})
for k in ("RUSTFLAGS","RUSTC_WRAPPER","RUSTC_WORKSPACE_WRAPPER","CARGO_ENCODED_RUSTFLAGS"): env.pop(k,None)
command={"phase":"aeneas","argv":argv,"cwd":str(W),"limits":limits,"cgroup":str(cg),"llbc_sha256":sha(llbc),"tool_pins":{str(a):cfg["aeneas_sha256"]},"charon_targets":json.loads((W/"runs-charon/declaration-inventory.json").read_text())["selected_transparent_targets"]}
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
status=proc.returncode
receipt={**command,"exit_status":status,"timed_out":timed,"wall_seconds":round(time.monotonic()-start,3),"swap_current_bytes":int((cg/"memory.swap.current").read_text()),"memory_peak_bytes":int((cg/"memory.peak").read_text()),"memory_events_before":before,"memory_events_after":(cg/"memory.events").read_text(),"finished_utc":time.strftime("%Y-%m-%dT%H:%M:%SZ",time.gmtime())}
txt=(run/"time.log").read_text(); m=re.search(r"Maximum resident set size \(kbytes\): (\d+)",txt); receipt["max_process_rss_kib"]=int(m.group(1)) if m else None
meta_path=gen/"translation.json"
if meta_path.exists():
 receipt["translation_sha256"]=sha(meta_path)
 receipt["generated_lean"]={str(p.relative_to(run)):sha(p) for p in sorted(gen.rglob("*.lean"))}
(run/"receipt.json").write_text(json.dumps(receipt,indent=2)+"\n")
if status != 0: sys.exit(status if status is not None else 1)
assert meta_path.exists(),"Aeneas exited 0 without translation metadata"
meta=json.loads(meta_path.read_text()); functions=meta.get("functions",[]); types=meta.get("types",[])
assert functions and types,"empty Aeneas translation"
# Require the exact source-spanned target functions and every generated field-file callee to be concrete.
expected={"QM31.square":("src/field.rs",951),"WideExact.mul_qm31":("src/field/wide_exact.rs",178)}
found={}
for f in functions:
 src=f.get("source") or {}; line=src.get("begin_line"); file=src.get("file","")
 for label,(want_file,want_line) in expected.items():
  if file==want_file and line==want_line:
   assert not f.get("is_opaque",True),(label,f)
   found[label]=f
 if file in ("src/field.rs","src/field/wide_exact.rs"):
  assert not f.get("is_opaque",True),(f.get("lean_name"),file,line)
assert set(found)==set(expected),(set(found),set(expected))
leanfiles={p.name:p.read_text() for p in gen.rglob("*.lean")}
for label,f in found.items():
 lean_name=f["lean_name"]
 fname=f.get("lean_file")
 body=(gen/fname).read_text()
 assert f"def {lean_name}" in body,(label,lean_name,fname)
receipt["translation_nonempty_assertion"]=True
receipt["generated_target_functions"]={k:{"lean_name":v["lean_name"],"lean_file":v["lean_file"],"source":v["source"],"is_opaque":v["is_opaque"]} for k,v in found.items()}
receipt["generated_field_function_count"]=sum(1 for f in functions if (f.get("source") or {}).get("file") in ("src/field.rs","src/field/wide_exact.rs"))
receipt["all_generated_field_functions_nonopaque"]=True
(run/"receipt.json").write_text(json.dumps(receipt,indent=2)+"\n")
print(json.dumps({"targets":receipt["generated_target_functions"],"generated_field_function_count":receipt["generated_field_function_count"],"all_generated_field_functions_nonopaque":True},indent=2))
