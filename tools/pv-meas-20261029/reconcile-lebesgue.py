"""D519 mechanical reconciliation. Uses D502's adopted per-module capped runner."""
import pathlib,json,subprocess,hashlib,re,shutil,time,sys
H=pathlib.Path('/home/dombarker/project-offloads/codex-pv-meas-20261029')
P=pathlib.Path('/home/dombarker/project-offloads/ZK-v7-one-tx-formal-consolidation-20260828/AspisFormal/.lake/packages/mathlib')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
x=json.loads((H/'evidence/cohort-check.json').read_text()); adds={v['module']:v for v in x['added']}
authfile=pathlib.Path('/home/dombarker/project-offloads/codex-pv-replay-20261027/evidence/external-object-manifest.json')
assert sha(authfile)==x['manifest_sha256']
auth={v['module'].replace('/','.'):v for v in json.loads(authfile.read_text())}
env=json.loads(pathlib.Path('/home/dombarker/project-offloads/codex-pv-evh-20261029/J.json').read_text())
assert subprocess.check_output([env['LEAN'],'--githash'],text=True).strip()==env['LEAN_GITHASH']
for d in ['objects','sources','evidence']:(H/d).mkdir(exist_ok=True,parents=True)
# Namespace completeness for all authoritative Mathlib modules: plain copies + companions.
for m,v in auth.items():
 p=pathlib.Path(v['path']);assert sha(p)==v['object_sha256'],('external changed',m)
 if m.split('.')[0]!='Mathlib':continue
 dst=H/'objects'/(m.replace('.','/')+'.olean');dst.parent.mkdir(parents=True,exist_ok=True)
 for suffix in ['.olean','.olean.server','.olean.private','.ilean','.ir']:
  src=p.with_suffix(suffix);out=dst.with_suffix(suffix)
  if src.exists() and (not out.exists() or sha(out)!=sha(src)):shutil.copyfile(src,out)
env['LEAN_PATH']=str(H/'objects')+':'+env['LEAN_PATH'];(H/'J.json').write_text(json.dumps(env))
roots=[pathlib.Path(r) for r in env['LEAN_PATH'].split(':')]
def resolve(m):
 rel=m.replace('.','/')+'.olean';ns=m.split('.')[0]
 r=next((r for r in roots if (r/ns).is_dir() or (r/rel).is_file()),None)
 assert r is not None,('no namespace',m)
 p=r/rel;assert p.exists(),('root shadowing',m,str(p));return p
checks=[]
for m,v in auth.items():
 p=resolve(m);assert sha(p)==v['object_sha256'],('effective external',m,str(p))
 checks.append(dict(module=m,path=str(p),sha256=sha(p)))
(H/'evidence/effective-authority.json').write_text(json.dumps(checks,indent=2))
order=[];seen=set()
def visit(m):
 if m in seen:return
 seen.add(m)
 for d in adds[m]['imports']:
  if d in adds:visit(d)
 order.append(m)
for m in json.loads((H/'evidence/lebegue-plan.json').read_text())['required']:visit(m)
(H/'evidence/rebuild-plan.json').write_text(json.dumps(dict(order=order,charged=False,reason='Independent Lebesgue expectation closure after immutable Gluing elaboration failure'),indent=2))
# ID inventory includes other workers' receipts and shared sent.txt, before any scope.
root=H.parent;used=set()
pat=re.compile(r'(?:^|[-_])(74\d{3})(?:[-_.]|$)')
for job in root.glob('codex-pv-*'):
 for q in job.glob('evidence/**/*'):
  if q.is_file():
   z=pat.search(q.name)
   if z:used.add(int(z[1]))
sent=root/'r1-privacy-build-integration-20261019/evidence/sent.txt'
for l in sent.read_text().splitlines():
 z=l.split()
 if len(z)>2 and z[2].isdigit():used.add(int(z[2]))
(H/'evidence/mechanical-id-audit.json').write_text(json.dumps(sorted(used)))
manifest=[]
for m in order:
 v=adds[m];prior=H/'evidence'/('module-'+m+'.json')
 if prior.exists():
  rec=json.loads(prior.read_text());assert rec['accepted'] and sha(resolve(m))==rec['object_sha256'];manifest.append(rec);continue
 deps={d:dict(path=str(resolve(d)),sha256=sha(resolve(d))) for d in v['imports']}
 a=next(a for a in range(74000,75000) if a not in used);used.add(a)
 src=pathlib.Path(v['source']);assert sha(src)==v['source_sha256']
 # Guard every previous elaboration failure, even across module names.
 for q in (H/'evidence').glob('receipt-74*.json'):
  old=json.loads(q.read_text());assert old['accepted'] or old['source_sha256']!=sha(src),('unchanged failed source',m)
 out=H/'objects'/(m.replace('.','/')+'.olean');out.parent.mkdir(parents=True,exist_ok=True)
 cmd=['systemd-run','--user','--scope','--quiet',f'--unit=pv-meas-{a}','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','/usr/bin/time','-v','-o',str(H/f'evidence/time-{a}.log'),'timeout','600','python3',str(root/'aspis-fs-generic-20261006/evidence/run2.py'),str(H/'J.json'),str(H/'objects'),str(P),str(out),str(src),'7000']
 rec=dict(attempt=a,target=m,charged=False,source_revision=sys.argv[1],source_mathlib_revision=x['mathlib_revision'],source_blob=v['source_blob'],source_sha256=sha(src),dependencies=deps,deps_fingerprint=hashlib.sha256(json.dumps(deps,sort_keys=True).encode()).hexdigest(),command=cmd,cohort_evidence='fresh one-module rebuild against hash-checked authority plus earlier addendum objects')
 (H/f'evidence/submission-{a}.json').write_text(json.dumps(rec,indent=2))
 retries=0
 while True:
  log=H/f'evidence/admission-{a}.log';admp=H/f'evidence/admission-{a}.json'
  with log.open('w') as f:r=subprocess.run(['python3',str(root/'codex-pv-runjoin-20261026/reservation-existing.py'),str(admp)],stdout=f,stderr=subprocess.STDOUT)
  adm=json.loads(admp.read_text()) if admp.exists() else None
  if r.returncode==0 and adm and adm.get('allowed') is True:break
  (H/f'evidence/refusal-{a}-{retries}.json').write_text(json.dumps(dict(exit=r.returncode,admission=adm,compiler_started=False,epoch=time.time())))
  print('REFUSAL',a,r.returncode,flush=True)
  if retries>=10:sys.exit(78)
  if r.returncode!=78 and adm is not None:sys.exit(r.returncode or 1)
  retries+=1;time.sleep(180)
 # Same process, admission immediately precedes launch. Never a stale admission snapshot.
 with (H/f'evidence/out-{a}.log').open('w') as f:r=subprocess.run(cmd,stdout=f,stderr=subprocess.STDOUT)
 rec['process_exit']=r.returncode;rec['admission']=adm
 tm=(H/f'evidence/time-{a}.log').read_text();log=(H/f'evidence/out-{a}.log').read_text()
 for key,pat in dict(exit=r'Exit status: (\d+)',peak_rss_kbytes=r'Maximum resident set size \(kbytes\): (\d+)',swaps=r'Swaps: (\d+)',wall=r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([0-9:.]+)').items():
  z=re.search(pat,tm);rec[key]=z[1] if z else None
 rec['axioms']='unchanged pinned external module; no new project theorem; no #print axioms emitted'
 rec['accepted']=r.returncode==0 and rec['exit']=='0' and 'error:' not in log and 'sorryAx' not in log
 if rec['accepted']:rec['object_sha256']=sha(out)
 (H/f'evidence/receipt-{a}.json').write_text(json.dumps(rec,indent=2))
 print(a,m,'PASS' if rec['accepted'] else 'FAIL',rec.get('wall'),rec.get('peak_rss_kbytes'),flush=True)
 if not rec['accepted']:print(log,flush=True);sys.exit(1)
 prior.write_text(json.dumps(rec,indent=2));manifest.append(rec)
 addendum=dict(original_manifest_sha256=x['manifest_sha256'],mathlib_revision=x['mathlib_revision'],required_count=len(order),roots=json.loads((H/'evidence/lebegue-plan.json').read_text())['roots'],modules=manifest)
 (H/'evidence/external-addendum-manifest.json').write_text(json.dumps(addendum,indent=2)+'\n')
 (H/'evidence/external-addendum-manifest.sha256').write_text(sha(H/'evidence/external-addendum-manifest.json')+'\n')
print('DONE',len(manifest),flush=True)
