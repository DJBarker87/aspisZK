"""Authorized sequential prerequisite chunk, run inside exactly one capped scope."""
import pathlib,sys,json,hashlib,subprocess,time,re,os
H=pathlib.Path('/home/dombarker/project-offloads/codex-pv-reach-20261027');P=H/'lean'
a=int(sys.argv[1]); assert 40200<=a<=40296
plan=json.load(open(H/f'evidence/resume9-plan-{a}.json'));E=H/'evidence'/f'resume9-{a}';E.mkdir(exist_ok=True)
env=json.load(open(P/'J.json')); start=time.monotonic(); records=[]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
cgroup=pathlib.Path('/sys/fs/cgroup')/next(l.split('::',1)[1].strip().lstrip('/') for l in pathlib.Path('/proc/self/cgroup').read_text().splitlines() if '::' in l)
aggregate_peak=0;memory_peak=0;swap_peak=0
for row in plan['modules']:
 m=row['module'];rel=m.replace('.','/');src=P/'sources'/(rel+'.lean');obj=P/'objects'/(rel+'.olean')
 assert src.is_file() and sha(src)==row['sha256'],m
 # Detach only our own output links; never write through a shared cache link.
 obj.parent.mkdir(parents=True,exist_ok=True)
 for q in obj.parent.glob(obj.stem+'.*'):
  if q.is_symlink():q.unlink()
 deps={}
 for d in row['transitive_imports']:
  q=P/'objects'/(d.replace('.','/')+'.olean')
  deps[d]=dict(path=str(q),sha256=sha(q)) if q.is_file() else None
 missing=[d for d,v in deps.items() if v is None]
 if missing:
  records.append(dict(module=m,source=row,exit=None,missing=missing));break
 cmd=['/usr/bin/time','-v','-o',str(E/(rel.replace('/','_')+'-time.log')),'timeout','900','python3','/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence/run2.py',str(P/'J.json'),str(P/'objects'),str(P/'sources'),str(obj),str(src),'7000']
 out=E/(rel.replace('/','_')+'-out.log');s=time.monotonic()
 with out.open('w') as f:
  proc=subprocess.Popen(cmd,stdout=f,stderr=subprocess.STDOUT)
  while proc.poll() is None:
   rss=0
   for pid in (cgroup/'cgroup.procs').read_text().split():
    try:
     st=pathlib.Path('/proc')/pid/'status';z=re.search(r'VmRSS:\s+(\d+)',st.read_text());rss+=int(z[1])*1024 if z else 0
    except (FileNotFoundError,ProcessLookupError):pass
   aggregate_peak=max(aggregate_peak,rss)
   memory_peak=max(memory_peak,int((cgroup/'memory.current').read_text()))
   swap_peak=max(swap_peak,int((cgroup/'memory.swap.current').read_text()))
   # The kernel hard limit enforces 8GiB; stop before reaching it.
   if rss>=8*1024**3: proc.terminate()
   time.sleep(.5)
 tim=(E/(rel.replace('/','_')+'-time.log')).read_text();txt=out.read_text()
 def metric(p):
  z=re.search(p,tim);return int(z[1]) if z else None
 rec=dict(module=m,source=row,command=cmd,dependencies=deps,deps_fingerprint=hashlib.sha256(json.dumps(deps,sort_keys=True).encode()).hexdigest(),exit=proc.returncode,wall_seconds=time.monotonic()-s,peak_rss_kib=metric(r'Maximum resident set size \(kbytes\): (\d+)'),swaps=metric(r'Swaps: (\d+)'),object_sha256=sha(obj) if obj.is_file() and proc.returncode==0 else None,axioms=re.findall(r"'[^']+' (?:depends on axioms: \[[\s\S]*?\]|does not depend on any axioms)",txt),output=txt,time_log=tim)
 rec['accepted']=proc.returncode==0 and 'sorryAx' not in txt and not re.search(r'(?m)^(?:.*:\d+:\d+: )?error:',txt)
 records.append(rec)
 (E/'modules.json').write_text(json.dumps(records,indent=2)+'\n')
 print(json.dumps({k:rec[k] for k in ['module','exit','wall_seconds','peak_rss_kib','accepted']}),flush=True)
 if not rec['accepted']:break
report=dict(attempt=a,source_revision=plan['source_revision'],plan=plan,environment=env,modules=records,wall_seconds=time.monotonic()-start,aggregate_rss_peak_bytes=aggregate_peak,cgroup_memory_sample_peak_bytes=memory_peak,cgroup_memory_peak_bytes=int((cgroup/'memory.peak').read_text()),swap_peak_bytes=swap_peak,accepted=len(records)==len(plan['modules']) and all(r.get('accepted') for r in records))
(E/'receipt.json').write_text(json.dumps(report,indent=2)+'\n')
sys.exit(0 if report['accepted'] else 1)
