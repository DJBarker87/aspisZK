from pathlib import Path
import hashlib,json,lzma,subprocess,time,os,sys
E=Path(__file__).resolve().parent;os.chdir(E)
R=E.parent;P=R/'codex-pv-evhc7-20261104';B=R/'codex-pv-evhc6-20261103';O=B/'objects';C=R/'codex-cx-fixture-cache-20261027'
def sha(p):
 h=hashlib.sha256()
 with open(p,'rb') as f:
  for b in iter(lambda:f.read(4*1024*1024),b''):h.update(b)
 return h.hexdigest()
def read(p):return json.loads(Path(p).read_text())
def save(n,v):Path(n).write_text(json.dumps(v,indent=2)+'\n')
start=time.monotonic(); checks=[]
try:
 assert not (E/'lean-92060').exists()
 collisions=[]
 for job in R.glob('codex-*'):
  for f in job.iterdir():
   if f.name in ['lean-92060','attempt-92060.json','admission-92060-0.json']:collisions.append(str(f))
 assert not collisions,collisions
 save('ID-AUDIT.json',dict(id=92060,collisions=collisions))
 runners={'reservation_agg16.py':'d6d40da5','S2W_lean_host_agg16.py':'9b325ab0','S2W_run_host_agg16.py':'8165ccff'}
 for n,prefix in runners.items():
  digest=sha(C/n);assert digest.startswith(prefix),(n,digest)
  checks.append(dict(path=str(C/n),sha256=digest,basis='lead runner pin'))
  if n!='reservation_agg16.py':
   (E/n).write_bytes((C/n).read_bytes());assert sha(E/n)==digest
 for n,digest in read(P/'inputs/AUTHORITY.json')['pins'].items():
  if (E/'inputs'/n).exists():assert sha(E/'inputs'/n)==digest,n
 cohort=[json.loads(l) for l in lzma.decompress((E/'inputs/NER_STREAM_B_COHORT.jsonl.xz').read_bytes()).splitlines()]
 assert len(cohort)==16058
 assert hashlib.sha256(lzma.decompress((E/'inputs/NER_STREAM_B_COHORT.jsonl.xz').read_bytes())).hexdigest()==read('inputs/NER_STREAM_B_COHORT_META.json')['cohort_sha256']
 authority={r['module']:r for r in cohort};rows=[json.loads(l) for l in Path('COMBINED-MANIFEST.jsonl').read_text().splitlines()];manifest={r['module']:r for r in rows}
 assert sha(P/'COMBINED-MANIFEST.jsonl')==read(P/'BLOCKED.json')['combined_manifest_sha256']
 prior={r['module']:r for r in map(json.loads,(P/'COMBINED-MANIFEST.jsonl').read_text().splitlines())}
 assert all(r==prior[r['module']] for r in rows if r['module']!='PV_BR_FixtureConsumer')
 loaded=set(read('EXPECTED-SCAN-MODULES.json'))
 pinchecks=[]
 for pin in read('inputs/NER_REBUILT_OBJECT_PINS.json'):
  m=pin['module'];assert authority[m]['object_sha256']==pin['sha256'];assert m in loaded,m
  assert manifest[m]['artifacts'][0]['sha256']==pin['sha256'],m
  pinchecks.append(dict(module=m,sha256=pin['sha256'],loaded=True))
 # Hash every combined manifest object and split companion, including all soundness objects.
 for i,r in enumerate(rows):
  m=r['module']
  if m=='PV_BR_FixtureConsumer':continue
  if m in authority:
   assert r['artifacts'][0]['sha256']==authority[m]['object_sha256'],m
   for c in authority[m]['companions']:
    assert any(a['sha256']==c['sha256'] and a['bytes']==c['bytes'] for a in r['artifacts']),c
  for a in r['artifacts']:
   f=Path(a['path']);assert not f.is_symlink() and f.stat().st_nlink==1,str(f)
   actual=sha(f);assert actual==a['sha256'] and f.stat().st_size==a['bytes'],dict(module=m,path=str(f),expected=a['sha256'],actual=actual)
   checks.append(dict(module=m,**a,loaded=m in loaded,basis='NER cohort' if m in authority else 'fresh overlay manifest'))
  if i%4000==0:print('HASHED',i,flush=True)
 # First namespace is complete; every dynamically loaded module resolves here.
 for m in loaded-{'PV_BR_FixtureConsumer'}:assert (O/(m.replace('.','/')+'.olean')).is_file(),m
 for n in ['PV_BR_FixtureConsumer.lean']:
  assert sha(n)=='48381d7a82300eadec1f5973cd87bd5b4119d1f399717d9210263e379ef1297e'
  assert sha(B/'sources'/n)==sha(n)
 assert not (O/'PV_BR_FixtureConsumer.olean').exists(),'consumer already compiled'
 scanner=Path('PV_NER_Scan.lean').read_text();driver=Path('inputs/NER_FinalDriverV2.lean').read_text()
 assert scanner[scanner.index('namespace NER'):scanner.index('end NER')+7]==driver[driver.index('namespace NER'):driver.index('end NER')+7]
 for n,digest in read('LOCAL-PINS.json').items():assert sha(n)==digest,n
 sysroot=Path('/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0')
 assert sha(sysroot/'bin/lean')==read('inputs/NER_STREAM_B_COHORT_META.json')['lean_binary_sha256']
 save('ALL-OBJECT-HASH-CHECKS.json',checks)
 save('PREFLIGHT.json',dict(status='PASS',wall_seconds=time.monotonic()-start,objects_and_companions=len(checks)-3,manifest_modules=len(rows),scan_modules=len(loaded),soundness_loaded_modules=len(loaded & authority.keys()),privacy_rebuilt_modules=594,explicit_soundness_pins=pinchecks,all_objects_verified_before_admission=True,scanner_namespace_identical=True,runner_hashes=checks[:3],checks_sha256=sha('ALL-OBJECT-HASH-CHECKS.json')))
 print('PREFLIGHT PASS',len(checks),flush=True)
except BaseException as exc:
 save('STOP.json',dict(status='PRE_ADMISSION_STOP',reason=repr(exc),step1='NOT_RUN',step2='NOT_RUN',step3='NOT_RUN',scope_launched=False));raise
