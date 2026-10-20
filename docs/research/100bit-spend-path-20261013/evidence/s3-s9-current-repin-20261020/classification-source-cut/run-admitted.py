from pathlib import Path
import argparse, contextlib, fcntl, io, json, os, runpy, re, subprocess, time
W=Path(__file__).resolve().parent
P=json.loads((W/"input/command-plan.json").read_text())
ap=argparse.ArgumentParser(); ap.add_argument("--phase",choices=["charon","aeneas"],required=True); phase=ap.parse_args().phase
G=1024**3; high=P["scope_memory_high_bytes"]; cap=P["scope_memory_max_bytes"]
collector=Path("/home/dombarker/project-offloads/r1-circle-sample-wrapper-extraction-v2/collect-cgroups.py")
lockpath=Path("/tmp/aspis-global-extraction-admission-20261019.lock")
unit=re.sub(r"[^a-zA-Z0-9_.-]","-",f"aspis-s3-inactive-{phase}-{os.getpid()}-{time.time_ns()}")
with lockpath.open("a") as lock:
 fcntl.flock(lock,fcntl.LOCK_EX)
 buf=io.StringIO()
 with contextlib.redirect_stdout(buf): runpy.run_path(str(collector))
 inv=json.loads(buf.getvalue()); rows=inv["all_populated_cgroups"]
 unc=[r for r in rows if r["max"]=="max" and (r["scope"] or (Path(r["path"]).name.endswith(".service") and not any(Path(r["path"]) in Path(s["path"]).parents for s in rows)))]
 outer=[r for r in unc if not any(Path(s["path"]) in Path(r["path"]).parents for s in unc)]
 usage=sum(r["current_bytes"] or 0 for r in outer); reserve=8*G; finite=inv["effective_sum_bytes"]
 checks={"finite_plus_candidate_le_48GiB":finite+cap<=48*G,"finite_plus_uncapped_and_reserve_le_MemTotal":finite+cap+usage+reserve<=inv["MemTotal_kB"]*1024,"MemAvailable_at_least_14GiB":inv["MemAvailable_kB"]*1024>=14*G}
 admission={"phase":phase,"inventory":inv,"outer_uncapped":outer,"candidate_cap_bytes":cap,"OS_reserve_bytes":reserve,"checks":checks}
 apath=W/("admission-"+phase+".json"); apath.write_text(json.dumps(admission,indent=2)+"\n")
 print(json.dumps({"phase":phase,"checks":checks,"finite_GiB":finite/G,"uncapped_GiB":usage/G}),flush=True)
 if not all(checks.values()): raise SystemExit("admission rejected; no extraction launched")
 cmd=["systemd-run","--user","--scope","--quiet","--unit="+unit,"-p","MemoryHigh="+str(high),"-p","MemoryMax="+str(cap),"-p","MemorySwapMax=0","-p","TasksMax=128","python3",str(W/"run-source-call-extraction.py"),"--root",str(W),"--phase",phase]
 proc=subprocess.Popen(cmd)
 deadline=time.monotonic()+10; registration=None
 while time.monotonic()<deadline and proc.poll() is None:
  q=subprocess.run(["systemctl","--user","show",unit+".scope","--property=ControlGroup","--value"],text=True,stdout=subprocess.PIPE,stderr=subprocess.DEVNULL)
  cg=q.stdout.strip()
  if q.returncode==0 and cg:
   d=Path("/sys/fs/cgroup")/cg.lstrip("/")
   try:
    limits={k:(d/k).read_text().strip() for k in ("memory.high","memory.max","memory.swap.max")}; populated="populated 1" in (d/"cgroup.events").read_text()
   except FileNotFoundError: time.sleep(.02); continue
   if limits=={"memory.high":str(high),"memory.max":str(cap),"memory.swap.max":"0"} and populated:
    registration={"scope":cg,"limits":limits,"populated":True,"registered_ns":time.time_ns()}; break
  time.sleep(.02)
 if registration is None:
  if proc.poll() is None: subprocess.run(["systemctl","--user","kill","--signal=TERM",unit+".scope"],stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL)
  status=proc.wait(); (W/("reservation-"+phase+".json")).write_text(json.dumps({"exit_status":status,"scope_registration":"not_verified"},indent=2)+"\n"); raise SystemExit("scope registration failed")
 registration["command"]=cmd; (W/("reservation-"+phase+".json")).write_text(json.dumps(registration,indent=2)+"\n")
 fcntl.flock(lock,fcntl.LOCK_UN)
raise SystemExit(proc.wait())
