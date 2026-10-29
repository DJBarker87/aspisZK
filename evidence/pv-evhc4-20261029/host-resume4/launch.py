"""Single admitted aggregation; reservation refusals retry, compile never retries."""
from pathlib import Path
import hashlib,json,subprocess,time,sys,os
B=Path('/home/dombarker/project-offloads/codex-pv-evhc-20261029'); E=B/'resume4'; os.chdir(B)
sha=lambda p:hashlib.file_digest(Path(p).open('rb'),'sha256').hexdigest()
v=json.load(open(E/'verified.json')); assert v['status']=='PASS'
ready=json.load(open(E/'READY.json'));assert ready['LEAN_PATH']==v['LEAN_PATH']
assert not (E/'LARGE-ATTEMPT-STARTED.json').exists(),'single attempt already submitted'
assert not (B/'lean-70700').exists(),'attempt already used'
assert sha(B/'sources/PV_EVH_FixtureConsumer.lean')==ready['consumer_source_sha256']
for name,h in v['runner_pins'].items():assert sha(B/name)==h,name
# Guard all existing receipts in the line. No proof/elaboration failure is exempt.
for job in B.parent.glob('codex-pv-evhc*-20261029'):
 for p in job.rglob('receipt.json'):
  old=json.load(open(p))
  assert not (old.get('exit_status')!=0 and ready['consumer_source_sha256'] in old.get('source_hashes',{}).values()),('failed source',str(p))
cfg=dict(kind='lean',module='PV_EVH_FixtureConsumer',attempt='lean-70700',sources=['sources/PV_EVH_FixtureConsumer.lean'],env={'LEAN_PATH':ready['LEAN_PATH']},timeout=600,command=['/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lake','env','lean','-j1','-M15000','-DElab.async=false','-o','objects/PV_EVH_FixtureConsumer.olean','sources/PV_EVH_FixtureConsumer.lean'],source_revision='5e9df8eb46b7ba32cde9b0eb430d93f5fc41fffd',source_original_path='lean/PV_EVH_FixtureConsumer.lean',authorization='User: Stream A LOG D526; one aggregation only',deps_fingerprint={'cohort_manifest_sha256':ready['cohort_manifest_sha256'],'ndr_manifest_sha256':ready['authoritative_ndr_manifest_sha256'],'first_root_preflight_sha256':ready['first_root_preflight_sha256'],'full_object_verification_sha256':sha(E/'verified.json'),'launch_guard_sha256':sha(E/'launch.py'),'prior_environment_correction':'D513 namespace-complete overlay; all 510 reconciled builds complete'},expected_time='import and final elaboration aggregation of the verified NDR and reconciled event closures; no dependency rebuild')
(E/'attempt-70700.json').write_text(json.dumps(cfg,indent=2)+'\n')
# Same process performs admission AND launch; never accepts just one signal.
for retry in range(21):
 admission=E/f'admission-70700-{retry}.json'; log=E/f'admission-70700-{retry}.log'
 with log.open('w') as out:r=subprocess.run(['python3',str(B/'reservation_agg16.py'),str(admission)],stdout=out,stderr=subprocess.STDOUT)
 a=json.load(open(admission)) if admission.exists() else None
 (E/f'admission-exit-70700-{retry}.json').write_text(json.dumps(dict(exit=r.returncode,allowed=a.get('allowed') if a else None,epoch=time.time(),compiler_started=False),indent=2)+'\n')
 if r.returncode==0 and a and a.get('allowed') is True:break
 if r.returncode==78 or (a and a.get('allowed') is False):
  print('REFUSED',retry,'exit',r.returncode,flush=True)
  if retry==20:sys.exit(78)
  # Complete 180 s cooldown; use short waits so monitoring can continue.
  until=time.monotonic()+180
  while time.monotonic()<until:time.sleep(min(30,until-time.monotonic()))
  continue
 print('INFRASTRUCTURE STOP',r.returncode,log.read_text(),flush=True);sys.exit(1)
command=['systemd-run','--user','--scope','--quiet','--unit=pv-evhc4-70700','-p','MemoryHigh=14G','-p','MemoryMax=16G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(B/'S2W_lean_host_agg16.py'),'resume4/attempt-70700.json']
# Exclusive marker makes resubmission impossible, including after transport loss.
with (E/'LARGE-ATTEMPT-STARTED.json').open('x') as f:json.dump(dict(attempt=70700,epoch=time.time(),command=command,admission=str(admission),admission_exit=r.returncode,allowed=a['allowed'],no_retry=True),f,indent=2)
print('START single attempt 70700',flush=True)
with (E/'launch-70700.log').open('w') as out:r=subprocess.run(command,stdout=out,stderr=subprocess.STDOUT)
(E/'launch-exit.json').write_text(json.dumps(dict(exit=r.returncode,epoch=time.time(),large_attempts=1,retry=False),indent=2)+'\n')
print('FINISHED launch exit',r.returncode,flush=True)
p=B/'lean-70700/receipt.json'
if p.exists():
 receipt=json.load(open(p)); print(json.dumps({k:receipt[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']}),flush=True)
else:print('NO RECEIPT; recover read-only; never resubmit',flush=True)
sys.exit(r.returncode)
