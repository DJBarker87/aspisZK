from pathlib import Path
import contextlib, fcntl, io, json, os, re, runpy, subprocess, sys, time, hashlib
W=Path(__file__).resolve().parent
assert sys.argv[1:]==['charon']
G=1024**3; high=2*G; cap=4*G; reserve=8*G
collector=Path('/home/dombarker/project-offloads/r1-circle-sample-wrapper-extraction-v2/collect-cgroups.py')
lockpath=Path('/tmp/aspis-global-extraction-admission-20261019.lock')
assert hashlib.sha256(collector.read_bytes()).hexdigest()=='4fc152ea4f88742fb460c301ae17446f1d1ba9162acdaafb37d80e60c4907800'
with lockpath.open('a') as lock:
 fcntl.flock(lock,fcntl.LOCK_EX)
 buf=io.StringIO()
 with contextlib.redirect_stdout(buf): runpy.run_path(str(collector))
 inv=json.loads(buf.getvalue()); rows=inv['all_populated_cgroups']
 unc=[r for r in rows if r['max']=='max' and (r['scope'] or (Path(r['path']).name.endswith('.service') and not any(Path(r['path']) in Path(s['path']).parents for s in rows)))]
 outer=[r for r in unc if not any(Path(s['path']) in Path(r['path']).parents for s in unc)]
 usage=0; working=[]
 for r in outer:
  q=Path(r['path']); current=int(r['current_bytes'] or 0); swap=0; clean=0
  try:
   current=max(current,int((q/'memory.current').read_text())); stats={k:int(v) for k,v in (x.split() for x in (q/'memory.stat').read_text().splitlines())}; swap=int((q/'memory.swap.current').read_text())
   clean=max(0,min(current,stats.get('inactive_file',0),stats.get('file',0))-stats.get('file_dirty',0)-stats.get('file_writeback',0))
  except (FileNotFoundError,ValueError): pass
  charged=current-clean+swap; usage+=charged; working.append({'path':str(q),'current':current,'swap':swap,'clean_inactive_file':clean,'charged':charged})
 finite=int(inv['effective_sum_bytes']); checks={'finite_plus_cap_le_48GiB':finite+cap<=48*G,'finite_plus_cap_uncapped_usage_and_os_reserve_le_MemTotal':finite+cap+usage+reserve<=int(inv['MemTotal_kB'])*1024,'available_after_cap_reserve_ge_14GiB':int(inv['MemAvailable_kB'])*1024-cap>=14*G}
 admission={'phase':'charon','inventory':inv,'uncapped_usage':working,'uncapped_charged_bytes':usage,'scope_high_bytes':high,'scope_max_bytes':cap,'swap_max_bytes':0,'os_reserve_bytes':reserve,'checks':checks,'profile':'fresh common-admission check for actual-core field types, WideExact.mul reachability cut Charon extraction'}
 d=W/'admission-charon'; d.mkdir(exist_ok=False)
 ap=d/'admission.json'; ap.write_text(json.dumps(admission,indent=2)+'\n')
 print(json.dumps({'timestamp_utc':inv['timestamp_utc'],'checks':checks,'finite_GiB':finite/G,'uncapped_GiB':usage/G}),flush=True)
 if not all(checks.values()): raise SystemExit('admission denied; no child launched')
 unit=re.sub(r'[^a-zA-Z0-9_.-]','-',f's9-helper-actual-wide-mul-charon-{os.getpid()}-{time.time_ns()}')
 cmd=['systemd-run','--user','--scope','--quiet','--unit='+unit,'-p',f'MemoryHigh={high}','-p',f'MemoryMax={cap}','-p','MemorySwapMax=0','-p','TasksMax=128','/usr/bin/env','PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin','python3',str(W/'run-stage-charon.py')]
 proc=subprocess.Popen(cmd); deadline=time.monotonic()+10; reg=None
 while time.monotonic()<deadline:
  if proc.poll() is not None: reg={'terminal_before_registration':True,'exit_status':proc.returncode}; break
  show=subprocess.run(['systemctl','--user','show',unit+'.scope','--property=ControlGroup','--value'],text=True,stdout=subprocess.PIPE,stderr=subprocess.DEVNULL); control=show.stdout.strip()
  if show.returncode==0 and control:
   cg=Path('/sys/fs/cgroup')/control.lstrip('/')
   try: limits={k:(cg/k).read_text().strip() for k in ('memory.high','memory.max','memory.swap.max')}; populated='populated 1' in (cg/'cgroup.events').read_text()
   except FileNotFoundError: time.sleep(.02); continue
   if limits=={'memory.high':str(high),'memory.max':str(cap),'memory.swap.max':'0'} and populated: reg={'control_group':control,'limits':limits,'populated':True}; break
  time.sleep(.02)
 if reg is None:
  subprocess.run(['systemctl','--user','kill','--signal=TERM',unit+'.scope'],stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL); proc.wait(); raise RuntimeError('owned scope failed verified cap check; child stopped')
 (d/'reservation.json').write_text(json.dumps({'unit':unit+'.scope','command':cmd,**reg},indent=2)+'\n')
 fcntl.flock(lock,fcntl.LOCK_UN)
 raise SystemExit(proc.wait())
