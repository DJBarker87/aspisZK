from pathlib import Path
import contextlib,fcntl,io,json,os,runpy,subprocess,sys,time
W=Path(__file__).resolve().parent;G=1024**3;high=3*G;cap=4*G;reserve=8*G
collector=Path('/home/dombarker/project-offloads/r1-circle-sample-wrapper-extraction-v2/collect-cgroups.py');lockpath=Path('/tmp/aspis-global-extraction-admission-20261019.lock')
with lockpath.open('a') as lock:
 fcntl.flock(lock,fcntl.LOCK_EX);buf=io.StringIO()
 with contextlib.redirect_stdout(buf):runpy.run_path(str(collector))
 inv=json.loads(buf.getvalue());rows=inv['all_populated_cgroups'];unc=[r for r in rows if r['max']=='max' and (r['scope'] or (Path(r['path']).name.endswith('.service') and not any(Path(r['path']) in Path(s['path']).parents for s in rows)))];outer=[r for r in unc if not any(Path(s['path']) in Path(r['path']).parents for s in unc)];usage=0;items=[]
 for r in outer:
  q=Path(r['path']);cur=int(r['current_bytes'] or 0);sw=0;clean=0
  try:
   cur=max(cur,int((q/'memory.current').read_text()));stats={k:int(v) for k,v in (x.split() for x in (q/'memory.stat').read_text().splitlines())};sw=int((q/'memory.swap.current').read_text());clean=max(0,min(cur,stats.get('inactive_file',0),stats.get('file',0))-stats.get('file_dirty',0)-stats.get('file_writeback',0))
  except (FileNotFoundError,ValueError):pass
  charged=cur-clean+sw;usage+=charged;items.append({'path':str(q),'charged_bytes':charged})
 finite=int(inv['effective_sum_bytes']);total=int(inv['MemTotal_kB'])*1024;avail=int(inv['MemAvailable_kB'])*1024;checks={'finite_plus_cap_le_48GiB':finite+cap<=48*G,'finite_cap_usage_reserve_le_memtotal':finite+cap+usage+reserve<=total,'available_after_cap_reserve_ge_14GiB':avail-cap>=14*G}
 adm={'phase':'qraw-v34-focused-owners','inventory':inv,'uncapped_outer_charged':items,'uncapped_charged_bytes':usage,'scope_high_bytes':high,'scope_max_bytes':cap,'swap_max_bytes':0,'os_reserve_bytes':reserve,'checks':checks}
 p=W/'admission.json';assert not p.exists();p.write_text(json.dumps(adm,indent=2)+'\n');print(json.dumps({'checks':checks,'finite_GiB':finite/G,'uncapped_charged_GiB':usage/G,'MemAvailable_GiB':avail/G}),flush=True)
 if not all(checks.values()): raise SystemExit('admission denied; no child launched')
 unit=f'fs-s9-qraw-v34-{os.getpid()}-{time.time_ns()}';cmd=['systemd-run','--user','--scope','--quiet','--unit='+unit,'-p',f'MemoryHigh={high}','-p',f'MemoryMax={cap}','-p','MemorySwapMax=0','-p','TasksMax=128','/usr/bin/env','PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin','python3',str(W/'run-stage.py')]
 p=subprocess.Popen(cmd);deadline=time.monotonic()+10;registered=None
 while time.monotonic()<deadline:
  if p.poll() is not None:registered={'terminal_before_registration':True,'exit_status':p.returncode};break
  show=subprocess.run(['systemctl','--user','show',unit+'.scope','--property=ControlGroup','--value'],text=True,stdout=subprocess.PIPE,stderr=subprocess.DEVNULL);control=show.stdout.strip()
  if show.returncode==0 and control:
   cg=Path('/sys/fs/cgroup')/control.lstrip('/')
   try:lim={k:(cg/k).read_text().strip() for k in ('memory.high','memory.max','memory.swap.max')};pop='populated 1' in (cg/'cgroup.events').read_text()
   except FileNotFoundError:time.sleep(.02);continue
   if lim=={'memory.high':str(high),'memory.max':str(cap),'memory.swap.max':'0'} and pop:registered={'control_group':control,'limits':lim,'populated':True};break
  time.sleep(.02)
 if registered is None:
  subprocess.run(['systemctl','--user','kill','--signal=TERM',unit+'.scope'],stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL);p.wait();raise RuntimeError('scope failed cap verification')
 reservation=W/'reservation.json';assert not reservation.exists();reservation.write_text(json.dumps({'unit':unit+'.scope','command':cmd,**registered},indent=2)+'\n');fcntl.flock(lock,fcntl.LOCK_UN);raise SystemExit(p.wait())
