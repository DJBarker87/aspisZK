"""D578 mechanical rebuild, one 6G/8G zero-swap scope per module."""
from pathlib import Path
import os,json,hashlib,subprocess,sys,time,importlib.util
B=Path(__file__).resolve().parent;os.chdir(B);R=B.parent
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
p=json.load(open('PLAN.json'));assert json.load(open('PREFLIGHT.json'))['status']=='PASS'
def save(n,v):Path(n).write_text(json.dumps(v,indent=2)+'\n')
def quiet_remaining():
 f=R/'QUIET_WINDOW.json'
 if not f.exists():return 0
 try:return max(0,float(json.load(open(f)).get('until',0))-time.time())
 except (OSError,ValueError):return 60
while quiet_remaining()>0:
 print('WAIT_QUIET_WINDOW',quiet_remaining(),flush=True);time.sleep(min(60,quiet_remaining()+1))
spec=importlib.util.spec_from_file_location('reservation_status',R/'codex-pv-runjoin-20261026/reservation-existing.py')
reservation_status=importlib.util.module_from_spec(spec);spec.loader.exec_module(reservation_status)
def wait_capacity():
 # Read-only reservation inventory is a planning observation, not a launch admission.
 # Keep the unchanged official admission immediately before the actual scope launch.
 while True:
  if quiet_remaining()>0:
   print('WAIT_QUIET_WINDOW',quiet_remaining(),flush=True);time.sleep(min(60,quiet_remaining()+1));continue
  try:
   rows=reservation_status.inventory(Path('/sys/fs/cgroup'))
   total=sum(r['charged_bytes'] for r in rows)
   if total+8*2**30<reservation_status.LIMIT:return
   print('WAIT_CAPACITY',total,flush=True)
  except OSError as e:print('WAIT_SNAPSHOT_RACE',str(e),flush=True)
  time.sleep(60)
nextid=91400
for m in p['order']:
 prior=[json.load(open(f)) for f in B.glob('lean-*/receipt.json')]
 assert all(v['exit_status']==0 or v['attempt']=='lean-91400' and json.load(open('OUTPUT-ENVIRONMENT-CORRECTION.json'))['failure_attempt']==91400 for v in prior),'failed receipt: stop'
 if any(v['module']==m and v['exit_status']==0 for v in prior):continue
 done={v['module'] for v in prior if v['exit_status']==0}
 assert all(d not in p['sources'] or d in done for d in p['edges'][m]),m
 src='sources/'+m.replace('.','/')+'.lean';assert sha(src)==p['sources'][m]['sha256']
 out='objects/'+m.replace('.','/')+'.olean';assert not Path(out).exists(),m
 Path(out).parent.mkdir(parents=True,exist_ok=True)
 while Path(f'attempt-{nextid}.json').exists():nextid+=1
 while True:
  wait_capacity()
  assert nextid<=91999,'rebuild ID budget exhausted';a=nextid;nextid+=1
  cfg=dict(kind='lean',module=m,attempt=f'lean-{a}',mechanical_reconciliation=True,charged_proof_attempt=False,sources=[src],env=dict(LEAN_PATH=p['LEAN_PATH']),timeout=600,command=[p['sysroot']+'/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-o',out,src],source_revision=p['sources'][m]['revision'],deps_fingerprint=dict(authority_manifest_sha256=sha('NER_STREAM_B_COHORT.jsonl.xz'),plan_sha256=sha('PLAN.json'),ruling="D578 h6'' coherent NER; ax1'; fresh overlay"),expected_time='mechanical focused recompilation, no source/proof change')
  save(f'attempt-{a}.json',cfg)
  with open(f'admission-{a}.log','w') as log:r=subprocess.run(['python3',str(R/'codex-pv-runjoin-20261026/reservation-existing.py'),f'admission-{a}.json'],stdout=log,stderr=subprocess.STDOUT)
  admission=json.load(open(f'admission-{a}.json'))
  if r.returncode==0 and admission['allowed'] is True:break
  if r.returncode==78 and admission['allowed'] is False:
   print('REFUSED',a,flush=True);time.sleep(180);continue
  raise RuntimeError(('admission infrastructure failure',a))
 print('START',a,m,flush=True)
 with open(f'launch-{a}.log','w') as log:r=subprocess.run(['systemd-run','--user','--scope','--quiet',f'--unit=pv-evhc6-{a}','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(B/'S2W_lean_host.py'),f'attempt-{a}.json'],stdout=log,stderr=subprocess.STDOUT)
 receipt=Path(f'lean-{a}/receipt.json')
 if not receipt.exists():save('STOP.json',dict(attempt=a,module=m,reason='missing receipt',launch_exit=r.returncode));sys.exit(1)
 v=json.load(open(receipt));print('DONE',a,m,v['exit_status'],v['wall_seconds'],v['peak_rss_kib'],flush=True)
 if r.returncode or v['exit_status'] or float(v['wall_seconds'])>=600 or int(v['peak_rss_kib'] or 0)>7*1024*1024:
  save('STOP.json',dict(attempt=a,module=m,reason='failed target or resource review; no retry',receipt=str(receipt),launch_exit=r.returncode));sys.exit(1)
 save('PROGRESS.json',dict(completed=len(done)+1,total=len(p['order']),last_id=a,last_module=m))
save('BUILDS-COMPLETE.json',dict(status='PASS',rebuilt=len(p['order']),last_id=a));print('BUILDS COMPLETE',flush=True)
