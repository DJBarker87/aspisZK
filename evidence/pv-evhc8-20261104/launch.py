from pathlib import Path
import json,subprocess,time,os,sys,hashlib
E=Path(__file__).resolve().parent;os.chdir(E)
R=E.parent;C=R/'codex-cx-fixture-cache-20261027'
def read(p):return json.loads(Path(p).read_text())
def save(n,v):Path(n).write_text(json.dumps(v,indent=2)+'\n')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert read('PREFLIGHT.json')['status']=='PASS'
assert not Path('attempt-92060.json').exists()
sources=['PV_BR_FixtureConsumer.lean','PV_NER_Scan.lean','NEP_Driver.lean','COMBINED-MANIFEST.jsonl','SCAN-ROOTS.json','EXPECTED-SCAN-MODULES.json','RAW-ROOTS.json','AUTHORIZATION.json','LOCAL-PINS.json','PREFLIGHT.json']
cfg=dict(kind='lean',module='PV_BR_FixtureConsumer + NER_SCAN + NEP_Driver combined closure',attempt='lean-92060',sources=sources,env=dict(LEAN_PATH=str(R/'codex-pv-evhc6-20261103/objects')+':/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean'),timeout=1850,command=['python3',str(E/'sequence.py')],source_revision=read('AUTHORIZATION.json')['revision'],deps_fingerprint=dict(manifest_sha256=sha('COMBINED-MANIFEST.jsonl'),preflight_sha256=sha('PREFLIGHT.json'),all_object_checks_sha256=sha('ALL-OBJECT-HASH-CHECKS.json'),sequence_sha256=sha('sequence.py'),local_pins_sha256=sha('LOCAL-PINS.json'),authority='coherent NER plus fresh 594 module overlay; D593',scope_id=92060),expected_time='consumer elaboration; then NER full closure scan; then 32 NEP raw dependency traversals; no finite-field aggregation; each stage timeout 600 seconds')
save('attempt-92060.json',cfg)
for retry in range(20):
 out=f'admission-92060-{retry}.json'
 for row in read('PREFLIGHT.json')['runner_hashes']:assert sha(row['path'])==row['sha256']
 with open(f'admission-92060-{retry}.log','w') as log:
  r=subprocess.run(['python3',str(C/'reservation_agg16.py'),out],stdout=log,stderr=subprocess.STDOUT)
 v=read(out) if Path(out).exists() else None
 save(f'admission-status-{retry}.json',dict(exit_status=r.returncode,receipt=out,allowed=v.get('allowed') if v else None,epoch=time.time(),scope_launched=False))
 if r.returncode==0 and v and v.get('allowed') is True:break
 if r.returncode==78 or (v and v.get('allowed') is False):
  print('ADMISSION REFUSED',retry,'waiting 180 seconds',flush=True)
  if retry<19:time.sleep(180);continue
 save('STOP.json',dict(status='ADMISSION_STOP',exit_status=r.returncode,receipt=out,scope_launched=False,step1='NOT_RUN',step2='NOT_RUN',step3='NOT_RUN'));sys.exit(1)
else:sys.exit(1)
print('ADMITTED; SINGLE SCOPE START',flush=True)
with open('launch-92060.log','w') as log:
 r=subprocess.run(['systemd-run','--user','--scope','--quiet','--unit=pv-evhc8-92060','-p','MemoryHigh=14G','-p','MemoryMax=16G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(E/'S2W_lean_host_agg16.py'),'attempt-92060.json'],stdout=log,stderr=subprocess.STDOUT)
save('LAUNCH-RESULT.json',dict(exit_status=r.returncode,attempts=1,scope='pv-evhc8-92060.scope',receipt='lean-92060/receipt.json'))
print('SCOPE DONE',r.returncode,flush=True)
sys.exit(r.returncode)
