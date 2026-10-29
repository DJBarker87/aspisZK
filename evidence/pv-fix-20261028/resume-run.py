from pathlib import Path
import subprocess,json,sys,time,hashlib,datetime
D=Path('/home/dombarker/project-offloads/codex-pv-fix-20261028');P=D.parent
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
a=int(sys.argv[1]);cohort=sys.argv[2];m=sys.argv[3].replace('.','/');assert 62100<=a<=62199
out=D/f'out-{a}.log';assert not out.exists(),a
cool=D/'last-refusal.json'
if cool.exists():assert time.time()-json.loads(cool.read_text())['epoch']>=180,'cooldown active'
assert len(list(D.glob('receipt-621*.json')))<40,'budget exhausted'
pre=json.loads((D/'preflight.json').read_text())[cohort];env=json.loads((D/'resume-env.json').read_text());O=D/cohort/'objects';S=D/cohort/'sources';source=S/(m+'.lean');obj=O/(m+'.olean');obj.parent.mkdir(parents=True,exist_ok=True);assert source.exists() and not obj.is_symlink()
rs=[O]+list(map(Path,env['LEAN_PATH'].split(':')));records={r['module'].replace('.','/'):r for r in pre['projects']};ext={r['module'].replace('.','/'):r for r in pre['external']};deps={}
def visit(n):
 if n in deps:return
 q=next((r/(n+'.olean') for r in rs if (r/(n+'.olean')).is_file()),None);
 if q is None:raise RuntimeError('missing pinned prerequisite '+n)
 if n in ext:assert sha(q)==ext[n]['object_sha256'];return
 r=records[n];s=Path(r['source']);assert sha(s)==r['source_sha256'],n
 fresh=[json.loads(f.read_text()) for f in sorted(D.glob('receipt-*.json'))];fr=[f for f in fresh if f['module']==n and f.get('exit')==0 and f['cohort']=='rdcd']
 expected=fr[-1]['object_sha256'] if fr else r['object_sha256'];assert sha(q)==expected,(n,q)
 if not fr:assert n in json.loads((D/'resume-cache-check.json').read_text()),('unverified cache',n)
 deps[n]=dict(source_sha256=sha(s),source_blob=r.get('source_blob'),object_path=str(q),object_sha256=sha(q))
 expected_imports={j['module'].replace('.','/'):j['object_sha256'] for j in r['imports']}
 if fr:
  for child,rec in fr[-1]['dependencies'].items():
   if child in expected_imports:expected_imports[child]=rec['object_sha256']
 for child,expected_hash in expected_imports.items():
  visit(child)
  actual=deps[child]['object_sha256'] if child in deps else ext[child]['object_sha256']
  assert actual==expected_hash,(n,child,'import fingerprint changed')
for l in source.read_text().splitlines():
 if l.startswith('import '):
  for n in l[7:].split():visit(n.replace('.','/'))
meta=json.loads((D/'resume-source-pins.json').read_text())[m];assert sha(source)==meta['sha256']
# Admission and launch deliberately share this invocation, and BOTH signals are checked.
ad=D/f'admission-{a}.json'
with (D/f'admission-{a}.log').open('a') as f:p=subprocess.run(['python3',str(P/'codex-pv-runjoin-20261026/reservation-existing.py'),str(ad)],stdout=f,stderr=subprocess.STDOUT)
if p.returncode!=0 or not ad.exists() or json.loads(ad.read_text()).get('allowed') is not True:
 cool.write_text(json.dumps(dict(epoch=time.time(),attempt=a,exit=p.returncode))+'\n');(D/f'refusal-{a}-{int(time.time())}.json').write_bytes(ad.read_bytes() if ad.exists() else b'{}');print('REFUSED',p.returncode);sys.exit(78)
cmd=['systemd-run','--user','--scope','--quiet','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(P/'codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy/barrier.py'),str(D/f'barrier-{a}.json'),'/usr/bin/time','-v','-o',str(D/f'time-{a}.log'),'timeout','900','python3',str(P/'aspis-fs-generic-20261006/evidence/run2.py'),str(D/'resume-env.json'),str(O),str(S),str(obj),str(source),'7000']
r=dict(attempt=a,module=m,cohort=cohort,source=meta,source_revision=(D/'resume-revision.txt').read_text().strip(),command=cmd,admission_exit=0,admission_allowed=True,launch_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),dependencies=deps,environment_sha256=sha(D/'resume-env.json'),limits=dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64),external_preflight_sha256=sha(D/'preflight.json'))
(D/f'env-{a}.json').write_bytes((D/'resume-env.json').read_bytes())
with out.open('w') as f:p=subprocess.run(cmd,stdout=f,stderr=subprocess.STDOUT)
if not (D/f'time-{a}.log').exists():
 cool.write_text(json.dumps(dict(epoch=time.time(),attempt=a,exit=p.returncode))+'\n');r.update(exit=p.returncode,compiler_launched=False);(D/f'receipt-{a}.json').write_text(json.dumps(r,indent=2)+'\n');print(out.read_text());sys.exit(78)
t=(D/f'time-{a}.log').read_text();o=out.read_text();r.update(exit=p.returncode,compiler_launched=True,wall=next(l.split(': ',1)[1] for l in t.splitlines() if 'Elapsed (wall clock)' in l),peak_rss_kib=int(next(l.split(': ',1)[1] for l in t.splitlines() if 'Maximum resident' in l)),swap=int(next(l.split(': ',1)[1] for l in t.splitlines() if 'Swaps:' in l)),axioms=[l for l in o.splitlines() if 'axioms' in l or "'sorryAx'" in l],object_sha256=sha(obj) if p.returncode==0 else None,errors=[l for l in o.splitlines() if 'error:' in l])
(D/f'receipt-{a}.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({k:r[k] for k in ['attempt','module','exit','wall','peak_rss_kib','swap','errors']}));print(o[:12000] if p.returncode else '');sys.exit(p.returncode)
