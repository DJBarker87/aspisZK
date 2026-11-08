"""Dependency-ordered replay batch inside ONE existing capped scope.
Uses unchanged pinned run2.py for every target. No package build.
"""
import json,pathlib,sys,subprocess,time,hashlib,re
V=pathlib.Path('/home/dombarker/project-offloads/codex-pv-lib-slice-20261107/v1-coherence');E=V/'evidence';S=V/'sources-canonical';O=V/'objects-canonical'
a=int(sys.argv[1]);assert 56500<=a<=56589
plan=json.load(open(V/'PLAN.json'));batch=json.load(open(E/f'batch-{a}.json'))
results=[]
for m in batch:
 s=S/(m+'.lean');o=O/(m+'.olean');assert not o.exists(),('immutable accepted artifact',m)
 deps=plan['rebuild'][m]['imports'];dep_hash={}
 for d in deps:
  if d=='Lean':continue
  p=O/(d.replace('.','/')+'.olean');assert p.exists(),('missing dependency',m,d)
  dep_hash[d]=hashlib.file_digest(p.open('rb'),'sha256').hexdigest()
 # A missing-module failure may repeat only once the named missing object exists.
 for prior in E.glob('receipt-*-'+m+'.json'):
  old=json.load(open(prior))
  if old.get('accepted'):continue
  oldlog=E/prior.name.replace('receipt-','out-').replace('.json','.log')
  if oldlog.exists():
   absent=re.findall(r"unknown module prefix '([^']+)'",oldlog.read_text())
   assert all((O/(d.replace('.','/')+'.olean')).exists() for d in absent),('unchanged missing dependency',m,absent)
 log=E/f'out-{a}-{m}.log';tim=E/f'time-{a}-{m}.log'
 cmd=['/usr/bin/time','-v','-o',str(tim),'timeout','600','python3','/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence/run2.py',str(V/'J.json'),str(O),str(S),str(o),str(s),'7000']
 t=time.time()
 with log.open('w') as f:r=subprocess.run(cmd,stdout=f,stderr=subprocess.STDOUT,cwd=V)
 out=log.read_text();rec=dict(attempt=a,target=m,source_revision=plan['revision'],source_sha256=hashlib.file_digest(s.open('rb'),'sha256').hexdigest(),source_origin=plan['rebuild'][m]['source_origin'],dependency_hashes=dep_hash,command=cmd,exit=r.returncode,wall_seconds=time.time()-t,accepted=r.returncode==0 and 'error:' not in out and 'sorryAx' not in out,axioms_summary_based=[l for l in out.splitlines() if 'axioms' in l])
 for line in tim.read_text().splitlines():
  for k,f in [('Maximum resident set size (kbytes):','peak_rss_kbytes'),('Swaps:','swaps'),('Elapsed (wall clock) time (h:mm:ss or m:ss):','wall')]:
   if k in line:rec[f]=line.split(k)[1].strip()
 if rec['accepted']:rec['object_sha256']=hashlib.file_digest(o.open('rb'),'sha256').hexdigest()
 (E/f'receipt-{a}-{m}.json').write_text(json.dumps(rec,indent=2));results.append(rec)
 print(json.dumps({k:rec.get(k) for k in ['attempt','target','exit','wall','peak_rss_kbytes','accepted']}),flush=True)
 if not rec['accepted']:
  print(out[-7000:],flush=True);sys.exit(1)
(E/f'results-{a}.json').write_text(json.dumps(results));sys.exit(0)
