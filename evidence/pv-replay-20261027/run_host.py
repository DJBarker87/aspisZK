"""Private serial replay using envfix's capped launcher; never writes shared inputs."""
from pathlib import Path
import sys,json,subprocess,hashlib,re,time,shutil,os
B=Path('/home/dombarker/project-offloads'); P=B/'codex-pv-replay-20261027'; E=P/'evidence';O=P/'objects'
plan=json.loads((P/'replay-plan.json').read_text()); nodes=plan['nodes']; env=json.loads((P/'env/J.json').read_text())
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def dump(p,d):p.write_text(json.dumps(d,indent=2)+'\n')
def append(p,d):
 with p.open('a') as f:f.write(json.dumps(d)+'\n')
paths=[Path(p) for p in env['LEAN_PATH'].split(':')]
def external(m):
 return next((p/(m+'.olean') for p in paths if (p/(m+'.olean')).is_file()),None)
def dep_record(m):
 p=O/(m+'.olean') if m in nodes else external(m)
 if p is None or not p.is_file():return None
 return dict(module=m,path=str(p),sha256=sha(p))
def norm(ds):return [(r['module'].replace('.','/'),r.get('sha256') or r.get('object_sha256')) for r in ds]
def companions(src,dst):
 dst.parent.mkdir(parents=True,exist_ok=True)
 for suffix in ['.olean','.olean.private','.olean.server','.ilean','.ir']:
  s=src.with_suffix(suffix);d=dst.with_suffix(suffix)
  if s.is_file():shutil.copy2(s,d)
# Only artifact receipts with an exact source SHA, dependency list and output SHA can justify reuse.
index={};count=0
receiptfiles=[B/'aspis-fs-generic-20261006/evidence/EJR_attempts.jsonl',B/'aspis-fs-generic-20261006/evidence/EJR_reuses.jsonl']
receiptfiles+=list(B.glob('codex-pv-*/evidence/receipt-*.json'))
for p in receiptfiles:
 try:rs=[json.loads(l) for l in p.read_text().splitlines() if l.strip()] if p.suffix=='.jsonl' else [json.loads(p.read_text())]
 except Exception:continue
 for r in rs:
  m=r.get('module','').replace('.','/')
  if m not in nodes or r.get('exit',0)!=0 or not r.get('object_sha256') or 'deps' not in r:continue
  if r.get('source_sha256')!=nodes[m]['source_sha256']:continue
  candidates=[]
  dc=r.get('driver_command',[])
  if '-o' in dc:candidates.append(Path(dc[dc.index('-o')+1]))
  if r.get('source','').endswith('.olean'):candidates.append(Path(r['source']))
  candidates.extend([p.parent.parent/'objects'/(m+'.olean'),p.parent.parent/'lean-objects'/(m+'.olean')])
  candidates.extend([x/(m+'.olean') for x in paths])
  index.setdefault(m,[]).append((r,str(p),candidates));count+=1
print('indexed exact-source receipts',count,'modules',len(index),flush=True)
# Record external import boundary pins; no library compile is ever attempted.
boundary=[]
for m in plan['direct_external_boundary']:
 p=external(m);assert p is not None,('missing pinned external',m)
 boundary.append(dict(module=m,path=str(p),sha256=sha(p),bytes=p.stat().st_size))
dump(E/'external-boundary.json',boundary)
# Lean resolves root namespaces once: mirror only external namespace files into the private root.
# Symbolic links are read-only retained package inputs, never compiler output targets.
external_prefixes={m.split('/')[0] for m in plan['direct_external_boundary']} | {'AeneasMeta','Batteries','Qq','Aesop','ProofWidgets','ImportGraph','LeanSearchClient','Plausible','Lake'}
external_bindings=[]
for prefix in external_prefixes:
 for base in paths:
  for src in [base/(prefix+suffix) for suffix in ['.olean','.olean.private','.olean.server','.ilean','.ir']]+[base/prefix]:
   if src.is_dir():
    for folder, dirs, files in os.walk(src,followlinks=True):
     for name in files:
      s=Path(folder)/name
      if s.is_file() and s.suffix in ['.olean','.ilean','.private','.server','.ir']:
       d=O/s.relative_to(base)
       if not d.exists() and not d.is_symlink():d.parent.mkdir(parents=True,exist_ok=True);d.symlink_to(s)
   elif src.is_file():
    d=O/src.relative_to(base)
    if not d.exists():d.symlink_to(src)
external_bindings=[dict(path=str(q.relative_to(O)),target=str(q.resolve()),bytes=q.stat().st_size) for prefix in sorted(external_prefixes) for q in (O/prefix).rglob('*') if q.is_file()]
dump(E/'external-loader-files.json',external_bindings)
loader_bindings=[dict(module=m,path=str(O/(m+'.olean')),companions={suffix:sha(O/(m+suffix)) for suffix in ['.olean','.olean.private','.olean.server'] if (O/(m+suffix)).is_file()}) for m in sorted(external_prefixes) if (O/(m+'.olean')).is_file()]
dump(E/'loader-bindings.json',loader_bindings)
loader_digest=hashlib.sha256(json.dumps(dict(top=loader_bindings,files=external_bindings),sort_keys=True).encode()).hexdigest()
# Restarting the controller only resumes recorded successful results; never reruns failed compiles.
results={}
if (E/'results.jsonl').exists():
 for l in (E/'results.jsonl').read_text().splitlines():
  r=json.loads(l);results[r['module']]=r
used=[int(p.stem.split('-')[-1]) for p in E.glob('receipt-*.json')]+[int(p.stem.split('-')[-1]) for p in E.glob('refusal-*.json')]
nextid=max([27999]+used)+1
compiled=sum(1 for p in E.glob('receipt-*.json'))
def admission(a):
 for retry in range(2):
  rp=E/f'reservation-{a}-{retry}.json';rl=E/f'reservation-{a}-{retry}.log'
  with rl.open('w') as f:rc=subprocess.run(['python3',str(B/'codex-cx-s2x-20261023/S2X_reservation.py'),str(rp)],stdout=f,stderr=subprocess.STDOUT).returncode
  if not rp.exists() and retry==0:time.sleep(30);continue
  if not rp.exists():raise RuntimeError('Reservation JSON missing after one retry')
  r=json.loads(rp.read_text())
  if r.get('allowed'):return r
  if rc not in [0,78]:raise RuntimeError(f'Reservation infrastructure failure: {rc}: {rl.read_text()}')
  dump(E/f'refusal-{a}.json',dict(attempt=a,charged=False,exit=rc,admission=r));return None

def compile_one(m,n,deps):
 global nextid,compiled
 if compiled>=600:return dict(module=m,status='budget-exhausted')
 fp=hashlib.sha256(json.dumps(dict(deps=deps,loader_bindings_sha256=loader_digest),sort_keys=True).encode()).hexdigest()
 for retry in range(11):
  a=nextid;nextid+=1;assert 28000<=a<=29999
  ad=admission(a)
  if ad is not None:break
  print('admission hold',a,'retry after 180s',flush=True);time.sleep(180)
 else:raise RuntimeError('Reservation blocked after ten retries; compile-free work required')
 cmd=['sh',str(P/'run-private.sh'),str(a),m,'J','7000','8',fp]
 start=time.monotonic()
 with (E/f'launcher-{a}.log').open('w') as f:outer=subprocess.run(cmd,stdout=f,stderr=subprocess.STDOUT).returncode
 tp=E/f'time-{a}.log';op=E/f'out-{a}.log'
 if not tp.exists():
  dump(E/f'refusal-{a}.json',dict(attempt=a,charged=False,exit=outer,log=(E/f'launcher-{a}.log').read_text()))
  raise RuntimeError('Launcher refusal: '+(E/f'launcher-{a}.log').read_text())
 compiled+=1;t=tp.read_text();out=op.read_text()
 def val(p):
  z=re.search(p,t);return z[1].strip() if z else None
 exit=int(val(r'Exit status:\s*(\d+)'))
 axioms=[' '.join(z.split()) for z in re.findall(r"^('.*?' (?:depends on axioms: \[[^\]]*\]|does not depend on any axioms))",out,re.M|re.S)]
 bad=[z for z in axioms if '[' in z and not set(z.split('[',1)[1].rstrip(']').replace(' ','').split(','))<={'propext','Classical.choice','Quot.sound'}]
 obj=O/(m+'.olean')
 r=dict(attempt=a,module=m,status='compiled' if exit==0 else 'failed',source_sha256=n['source_sha256'],source_revision=plan['revision'],source_repository_path=n['source_path'],deps=deps,deps_fingerprint=fp,source_closure_fingerprint=n['deps_fingerprint'],command=cmd,launcher_sha256=sha(P/'run-private.sh'),env_sha256=sha(P/'env/J.json'),loader_bindings_sha256=loader_digest,exit=exit,validation_exit=90 if bad else exit,outer_exit=outer,wall_seconds=time.monotonic()-start,wall=val(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): (.+)'),peak_rss_kib=int(val(r'Maximum resident set size \(kbytes\):\s*(\d+)')),swaps=int(val(r'Swaps:\s*(\d+)')),axioms=axioms,axioms_status='printed' if axioms else 'no #print axioms in original source; final closure audit pending',errors=[l for l in out.splitlines() if 'error:' in l],nonstandard_axioms=bad,admission=ad,caps=dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64,lean_M=7000),object_sha256=sha(obj) if exit==0 and obj.exists() else None,object_bytes=obj.stat().st_size if exit==0 and obj.exists() else None)
 dump(E/f'receipt-{a}.json',r)
 print(a,m,r['status'],r['wall'],r['errors'][:2],flush=True)
 return r

def main():
 for m in plan['order']:
  if m in results:continue
  n=nodes[m];blocked=[d for d in n['imports'] if d in nodes and results.get(d,{}).get('status') not in ['compiled','reused']]
  if blocked:r=dict(module=m,status='blocked',dependencies=blocked)
  else:
   deps=[dep_record(d) for d in n['imports']];assert all(d is not None for d in deps),(m,'missing dep object')
   match=None
   for prior,receipt,candidates in reversed(index.get(m,[])):
    if norm(prior['deps'])!=norm(deps):continue
    for obj in candidates:
     if obj.is_file() and sha(obj)==prior['object_sha256']:match=(prior,receipt,obj);break
    if match:break
   if match:
    prior,receipt,obj=match;dst=O/(m+'.olean');companions(obj,dst)
    r=dict(module=m,status='reused',source_sha256=n['source_sha256'],source_revision=plan['revision'],source_repository_path=n['source_path'],deps=deps,source_closure_fingerprint=n['deps_fingerprint'],object_sha256=sha(dst),object_bytes=dst.stat().st_size,prior_receipt=receipt,prior_attempt=prior.get('attempt') or prior.get('compiled_attempt'),prior_object_path=str(obj),reason='exact source SHA and all direct dependency object SHAs match a successful compile receipt')
   elif '--preflight' in sys.argv:r=dict(module=m,status='needs-compile')
   else:
    r=compile_one(m,n,deps)
    if r.get('status')=='failed' and any(('failed to open file' in e or 'does not exist' in e or 'missing IR data file' in e or 'missing data file' in e) for e in r.get('errors',[])):
     append(E/'results.jsonl',r);raise RuntimeError('Stop on first loader/environment failure; receipt retained')
  results[m]=r;append(E/'results.jsonl',r)
 summary={s:sum(r['status']==s for r in results.values()) for s in sorted({r['status'] for r in results.values()})};dump(E/'summary.json',dict(revision=plan['revision'],project_count=len(nodes),counts=summary,charged_compiles=compiled,next_attempt=nextid));print('PROGRESS',len(results),summary,flush=True)
if __name__=='__main__':main()
