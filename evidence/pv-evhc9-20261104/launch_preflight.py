from pathlib import Path
import subprocess,json,hashlib,time,sys,os
E=Path(__file__).resolve().parent;os.chdir(E)
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
meta=json.load(open('PREFLIGHT-INPUTS.json'))
for n,h in meta['files'].items():assert sha(n)==h,n
for n,h in meta['runners'].items():assert sha(n)==h,n
assert not Path('attempt-92070.json').exists() and not Path('lean-92070').exists()
cfg=dict(kind='lean',module='D595 driver-only small-closure preflight and NEP planted cases',attempt='lean-92070',sources=list(meta['files']),env={'LEAN_PATH':str(E)+':/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean'},timeout=1000,command=['python3',str(E/'preflight_sequence.py')],source_revision=meta['revision'],deps_fingerprint={'input_pins':meta,'scope_id':92070,'release_closure_not_loaded':True},expected_time='small fixture elaboration and raw dependency traversals; no aggregation or arithmetic reduction')
Path('attempt-92070.json').write_text(json.dumps(cfg,indent=2)+'\n')
for retry in range(11):
 n=f'admission-92070-{retry}.json'
 with open(f'admission-92070-{retry}.log','w') as log:r=subprocess.run(['python3',meta['reservation'],n],stdout=log,stderr=subprocess.STDOUT)
 v=json.load(open(n))
 if r.returncode==0 and v.get('allowed') is True:break
 if r.returncode==78 or v.get('allowed') is False:
  if retry<10:print('REFUSED',retry,flush=True);time.sleep(180);continue
 sys.exit('normal admission failed; no scope launched')
with open('launch-92070.log','w') as log:r=subprocess.run(['systemd-run','--user','--scope','--quiet','--unit=pv-evhc9-92070','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(E/'S2W_run_host.py'),'attempt-92070.json'],stdout=log,stderr=subprocess.STDOUT)
Path('LAUNCH-RESULT.json').write_text(json.dumps(dict(exit_status=r.returncode,scope='pv-evhc9-92070.scope',id=92070,agg16_requested=False),indent=2)+'\n');sys.exit(r.returncode)
