from pathlib import Path
import hashlib,json,subprocess,os,time,sys,lzma
H=Path(__file__).resolve().parent;os.chdir(H)
R=H.parent;D=R/'codex-pv-evhc9-20261104';P=R/'codex-pv-evhc8-20261104';O=R/'codex-pv-evhc6-20261103/objects'
def read(p):return json.loads(Path(p).read_text())
def save(n,v):Path(n).write_text(json.dumps(v,indent=2)+'\n')
def sha(p):
 h=hashlib.sha256()
 with open(p,'rb') as f:
  for b in iter(lambda:f.read(4*1024*1024),b''):h.update(b)
 return h.hexdigest()
start=time.monotonic()
try:
 pins=read('COMMITTED-INPUT-PINS.json');auth=read('AUTHORIZATION.json')
 for n,h in pins.items():assert sha(R/n)==h,n
 runners=read(P/'PREFLIGHT.json')['runner_hashes']
 for r in runners:assert sha(r['path'])==r['sha256'],r
 assert sha(P/'S2W_run_host_agg16.py')==runners[2]['sha256']
 assert sha(P/'S2W_lean_host_agg16.py')==runners[1]['sha256']
 assert sha(D/'NEP_WALKER.olean')=='1abdef8e47ed6038186ab40a6e4bea354096d351d0431eb6a6fa81f70508d2e6'
 collisions=[]
 for job in R.glob('codex-*'):
  for n in ['lean-92080','attempt-92080.json','agg-92080']:
   if (job/n).exists():collisions.append(str(job/n))
 assert not collisions,collisions
 cohort_bytes=lzma.decompress((P/'inputs/NER_STREAM_B_COHORT.jsonl.xz').read_bytes())
 assert hashlib.sha256(cohort_bytes).hexdigest()==read(P/'inputs/NER_STREAM_B_COHORT_META.json')['cohort_sha256']
 cohort={r['module']:r for r in map(json.loads,cohort_bytes.splitlines())};assert len(cohort)==16058
 manifest={r['module']:r for r in map(json.loads,(P/'COMBINED-MANIFEST.jsonl').read_text().splitlines())}
 checks=read(P/'ALL-OBJECT-HASH-CHECKS.json'); indexed={r['path']:r for r in checks}
 loaded=set(read(P/'EXPECTED-SCAN-MODULES.json'));assert len(loaded)==16539
 for m,c in cohort.items():
  r=manifest[m];assert r['artifacts'][0]['sha256']==c['object_sha256'],m
  for a in c['companions']:assert any(x['sha256']==a['sha256'] and x['bytes']==a['bytes'] for x in r['artifacts']),m
 for pin in read(P/'inputs/NER_REBUILT_OBJECT_PINS.json'):
  m=pin['module'];assert m in loaded and cohort[m]['object_sha256']==pin['sha256'] and manifest[m]['artifacts'][0]['sha256']==pin['sha256'],m
 for m,r in manifest.items():
  if m=='PV_BR_FixtureConsumer':continue
  for a in r['artifacts']:assert indexed[a['path']]['sha256']==a['sha256'],a
 for i,r in enumerate(checks):
  f=Path(r['path']);assert sha(f)==r['sha256'],r
  if 'bytes' in r:assert f.stat().st_size==r['bytes'] and not f.is_symlink() and f.stat().st_nlink==1,r
  if i%8000==0:print('HASHED',i,flush=True)
 assert all((O/(m.replace('.','/')+'.olean')).is_file() for m in loaded-{'PV_BR_FixtureConsumer'})
 # Fresh snapshot names under the runner base; originals remain untouched.
 S=P/'evhc10-92080';S.mkdir(exist_ok=False);sources=[]
 for rel,h in pins.items():
  p=R/rel; dest=S/rel;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(p.read_bytes());sources.append(str(dest.relative_to(P)))
 for n in ['AUTHORIZATION.json','COMMITTED-INPUT-PINS.json','controller.py']:
  (S/n).write_bytes((H/n).read_bytes());sources.append(str((S/n).relative_to(P)))
 pre=dict(status='PASS',wall_seconds=time.monotonic()-start,revision=auth['revision'],checked_objects_and_runners=len(checks),cohort_modules=len(cohort),scan_modules=len(loaded),runner_hashes=runners,compiled_walker_sha256=sha(D/'NEP_WALKER.olean'),source_pins=pins,collisions=collisions,quiet_window=read(R/'QUIET_WINDOW.json'),epoch=time.time())
 save('PREFLIGHT.json',pre)
 cfg=dict(kind='lean',module='PV_BR_FixtureConsumer + NER_SCAN + NEP_Driver final (32 roots)',attempt='lean-92080',sources=sources,env={'LEAN_PATH':f'{D}:{O}:/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean'},timeout=1850,command=['python3',str(D/'AGG-SEQUENCE.py'),str(D/'agg-92080'),auth['revision']],source_revision=auth['revision'],deps_fingerprint={'scope_id':92080,'preflight':pre,'all_object_pins_sha256':sha(P/'ALL-OBJECT-HASH-CHECKS.json'),'authority':'NER coherent cohort plus fresh privacy overlay; D596'},expected_time='consumer elaboration, full closure incoherence scan, then 32 raw dependency walks; no arithmetic aggregation')
 (P/'attempt-92080.json').write_text(json.dumps(cfg,indent=2)+'\n');save('attempt-92080.json',cfg)
 for retry in range(20):
  for r in runners:assert sha(r['path'])==r['sha256']
  n=f'admission-92080-{retry}.json'
  with open(f'admission-92080-{retry}.log','w') as log:r=subprocess.run(['python3',runners[0]['path'],str(H/n)],stdout=log,stderr=subprocess.STDOUT)
  v=read(n) if Path(n).exists() else None
  save(f'admission-status-{retry}.json',dict(exit_status=r.returncode,allowed=v.get('allowed') if v else None,epoch=time.time(),scope_launched=False))
  if r.returncode==0 and v and v.get('allowed') is True:break
  if r.returncode==78 or (v and v.get('allowed') is False):
   print('REFUSED',retry,'waiting 180 seconds',flush=True)
   if retry<19:time.sleep(180);continue
  raise RuntimeError('admission failed; no scope launched')
 # Final source checks immediately before the sole launch.
 for n,h in pins.items():assert sha(R/n)==h,n
 print('ADMITTED; ONE SCOPE 92080',flush=True)
 with open('launch-92080.log','w') as log:r=subprocess.run(['systemd-run','--user','--scope','--quiet','--unit=pv-evhc-92080','-p','MemoryHigh=14G','-p','MemoryMax=16G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(P/'S2W_run_host_agg16.py'),'attempt-92080.json'],stdout=log,stderr=subprocess.STDOUT)
 save('LAUNCH-RESULT.json',dict(exit_status=r.returncode,attempts=1,scope='pv-evhc-92080.scope',receipt=str(P/'lean-92080/receipt.json')))
 print('SCOPE DONE',r.returncode,flush=True);sys.exit(r.returncode)
except Exception as exc:
 save('STOP.json',dict(reason=repr(exc),steps=['NOT_RUN']*3,scope_launched=False));raise
