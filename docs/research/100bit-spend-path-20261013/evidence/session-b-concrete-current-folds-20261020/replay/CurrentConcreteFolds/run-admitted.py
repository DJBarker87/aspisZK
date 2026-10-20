from pathlib import Path
import argparse,contextlib,fcntl,hashlib,io,json,os,re,runpy,subprocess,time
W=Path(__file__).resolve().parent
C=json.loads((W/'config.json').read_text())
ap=argparse.ArgumentParser();ap.add_argument('--phase',required=True,choices=[x['phase'] for x in C['stages']]);phase=ap.parse_args().phase
G=1024**3;cap=int(C.get('scope_memory_max_bytes',2*G));high=int(C.get('scope_memory_high_bytes',G))
assert 0<high<=cap
collector=Path(C['collector']);assert hashlib.sha256(collector.read_bytes()).hexdigest()==C['collector_sha256']
unit=re.sub(r'[^a-zA-Z0-9_.-]','-',f"aspis-{C.get('unit','focused')}-{phase}-{os.getpid()}-{time.time_ns()}")
process=None
with open(C['global_lock'],'a') as lock:
 fcntl.flock(lock,fcntl.LOCK_EX)
 buf=io.StringIO()
 with contextlib.redirect_stdout(buf):runpy.run_path(str(collector))
 inv=json.loads(buf.getvalue());rows=inv['all_populated_cgroups']
 unc=[r for r in rows if r['max']=='max' and (r['scope'] or (Path(r['path']).name.endswith('.service') and not any(Path(r['path']) in Path(s['path']).parents for s in rows)))]
 outer=[r for r in unc if not any(Path(s['path']) in Path(r['path']).parents for s in unc)]
 # Reserve uncapped working memory, swapped pages, and dirty/writeback pages.
 # Clean inactive file cache is reclaimable; charging it as live anonymous
 # memory unnecessarily serializes independent proof jobs after file copies.
 working=[]
 for row in outer:
  q=Path(row['path']);current=int(row['current_bytes'] or 0)
  entry={'path':str(q),'snapshot_current_bytes':current}
  try:
   current=max(current,int((q/'memory.current').read_text()))
   stats={k:int(v) for k,v in (line.split() for line in (q/'memory.stat').read_text().splitlines())}
   swap=int((q/'memory.swap.current').read_text())
   clean=max(0,min(current,stats.get('inactive_file',0),stats.get('file',0))-stats.get('file_dirty',0)-stats.get('file_writeback',0))
  except (FileNotFoundError,ValueError):
   clean=0;swap=0;stats={}
  charged=current-clean+swap
  entry.update(current_bytes=current,clean_inactive_file_bytes=clean,swap_current_bytes=swap,charged_bytes=charged,memory_stat=stats)
  working.append(entry)
 usage=sum(r['charged_bytes'] for r in working);reserve=8*G;finite=inv['effective_sum_bytes']
 checks={'finite_plus_candidate_le_48GiB':finite+cap<=48*G,'finite_plus_uncapped_and_reserve_le_MemTotal':finite+cap+usage+reserve<=inv['MemTotal_kB']*1024,'MemAvailable_at_least_14GiB':inv['MemAvailable_kB']*1024>=14*G}
 report={'phase':phase,'inventory':inv,'outermost_uncapped_execution_nodes':outer,'uncapped_working_memory_accounting':working,'uncapped_accounting_rule':'current - clean inactive file + swap; dirty and writeback retained; growth reserve separate','candidate_cap_bytes':cap,'OS_growth_reserve_bytes':reserve,'checks':checks,'launcher_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'unit':unit+'.scope'}
 admission=W/('admission-'+phase+'.json');assert not admission.exists();admission.write_text(json.dumps(report,indent=2)+'\n')
 print(json.dumps({'phase':phase,'checks':checks,'finite_reserved_GiB':finite/G,'uncapped_current_GiB':usage/G,'scope':unit+'.scope'}),flush=True)
 assert all(checks.values()),'admission rejected; no job started'
 cmd=['systemd-run','--user','--scope','--quiet','--unit='+unit,'-p','MemoryHigh='+str(high),'-p','MemoryMax='+str(cap),'-p','MemorySwapMax=0','-p','TasksMax=128','python3',str(W/'run-stage.py'),phase]
 process=subprocess.Popen(cmd)
 deadline=time.monotonic()+10
 registration=None
 while time.monotonic()<deadline:
  code=process.poll()
  if code is not None:
   registration={'terminal_before_registration':True,'exit_status':code};break
  r=subprocess.run(['systemctl','--user','show',unit+'.scope','--property=ControlGroup','--value'],text=True,stdout=subprocess.PIPE,stderr=subprocess.DEVNULL)
  control=r.stdout.strip()
  if r.returncode==0 and control:
   cg=Path('/sys/fs/cgroup')/control.lstrip('/')
   try:
    limits={k:(cg/k).read_text().strip() for k in ['memory.high','memory.max','memory.swap.max']}
    populated='populated 1' in (cg/'cgroup.events').read_text()
   except FileNotFoundError: time.sleep(.02);continue
   if limits=={'memory.high':str(high),'memory.max':str(cap),'memory.swap.max':'0'} and populated:
    registration={'terminal_before_registration':False,'control_group':control,'limits':limits,'populated':True,'registered_time_ns':time.time_ns()};break
  time.sleep(.02)
 if registration is None:
  subprocess.run(['systemctl','--user','kill','--signal=TERM',unit+'.scope'],stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL)
  process.wait();raise RuntimeError('scope reservation was not verified; own job terminated')
 registration['command']=cmd;registration['lock_release_time_ns']=time.time_ns()
 (W/('reservation-'+phase+'.json')).write_text(json.dumps(registration,indent=2)+'\n')
 fcntl.flock(lock,fcntl.LOCK_UN)
# The registered populated finite scope is now included in subsequent admissions.
# Waiting outside the admission lock permits independent scoped jobs to overlap.
raise SystemExit(process.wait())
