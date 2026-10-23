from pathlib import Path
import hashlib,json,os,re,signal,subprocess,sys,time
W=Path(__file__).resolve().parent
cfg=json.loads((W/"attempt-config.json").read_text())
llbc=W/"runs-charon/actual-current-checkpoint-k.llbc"
assert llbc.exists()
d=json.loads(llbc.read_text()); assert not d.get("has_errors"), d.get("errors")
found=[]
for f in d["translated"]["fun_decls"]:
    if not isinstance(f, dict):
        continue
    meta=f.get("item_meta") or {}
    txt=meta.get("source_text") or ""
    if "pub fn checkpoint_qm_decoder(" in txt or "fn checkpoint_qm_decoder(" in txt: found.append({"opacity":meta.get("opacity"),"span":meta.get("span")})
assert found, "Charon output does not contain source checkpoint_qm_decoder function"
a=Path(cfg["aeneas_path"]); sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(a)==cfg["aeneas_sha256"]
cgline=Path("/proc/self/cgroup").read_text().strip(); assert cgline.startswith("0::"),cgline
cg=Path("/sys/fs/cgroup")/cgline[3:].lstrip("/")
limits={k:(cg/k).read_text().strip() for k in ("memory.high","memory.max","memory.swap.max")}
want={"memory.high":str(cfg["scope_memory_high_bytes"]),"memory.max":str(cfg["scope_memory_max_bytes"]),"memory.swap.max":"0"}
assert limits==want,(limits,want)
run=W/"runs-aeneas"; run.mkdir(exist_ok=False); gen=run/"generated"
argv=[str(Path(cfg["aeneas_path"])),"-sequential","-no-progress-bar","-abort-on-error","-backend","lean","-namespace","AspisR1S9CurrentCheckpointKDecoderV1","-dest",str(gen),"-subdir","AspisR1S9CurrentCheckpointKDecoderV1","-split-files","-emit-json",str(llbc)]
env=os.environ.copy(); env.update({"PATH":"/home/dombarker/.cargo/bin:/usr/bin:/bin"})
for k in ("RUSTFLAGS","RUSTC_WRAPPER","RUSTC_WORKSPACE_WRAPPER","CARGO_ENCODED_RUSTFLAGS"): env.pop(k,None)
command={"phase":"aeneas","argv":argv,"cwd":str(W),"limits":limits,"cgroup":str(cg),"llbc_sha256":sha(llbc),"tool_pins":{str(a):cfg["aeneas_sha256"]},"transparent_build_declarations":found}
(run/"command.json").write_text(json.dumps(command,indent=2)+"\n"); (run/"environment.json").write_text(json.dumps({k:env[k] for k in ("PATH",)},indent=2)+"\n")
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
if status==0:
    meta=json.loads((gen/"translation.json").read_text())
    names=[x.get("lean_name","") for x in meta.get("functions",[])]
    assert meta.get("functions") and meta.get("types"),"Aeneas emitted empty translation"
    assert any("checkpoint_qm_decoder" in n for n in names),names
sys.exit(status if status is not None else 1)
