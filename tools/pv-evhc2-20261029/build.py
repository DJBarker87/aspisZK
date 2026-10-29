"""Mechanical reconciliation only. Normal unchanged runner, one admitted module per scope."""
from pathlib import Path
import json,subprocess,hashlib,time,sys,os
B=Path(__file__).resolve().parent;os.chdir(B)
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
plan=json.load(open('plan.json'));used=json.load(open('id-audit.json'))
assert json.load(open('preflight.json'))['status']=='PASS'
assert all(v['identical'] and (v['kind']=='project' or v['host_matches_common_source']) for v in json.load(open('source-identity-host.json'))['modules'])
ndr=B.parent/'codex-cx-reconcile-cache-20261028/objects'
sysroot='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0'
leanpath=str(B/'objects')+':'+str(ndr)+':'+sysroot+'/lib/lean'
start=time.monotonic();nextid=71000
for m in plan['rebuild']:
 old=list(B.glob('lean-*/receipt.json'))
 for p in old:
  v=json.load(open(p))
  assert v['exit_status']==0,('prior failed module: stop, no unchanged retry',str(p))
 prior=[json.load(open(p)) for p in old if json.load(open(p)).get('module')==m]
 if prior:continue
 while str(nextid) in used or (B/f'lean-{nextid}').exists():nextid+=1
 assert nextid<=71999
 a=nextid;nextid+=1
 src='sources/'+m.replace('.','/')+'.lean';assert sha(src)==plan['sources'][m]['sha256']
 # Source-only guard required by ruling (u), over this line's local receipts.
 for p in old:
  v=json.load(open(p));assert v['exit_status']==0 or sha(src) not in v['source_hashes'].values(),str(p)
 cfg=dict(kind='lean',module=m,attempt=f'lean-{a}',mechanical_reconciliation=True,charged_proof_attempt=False,sources=[src],env=dict(LEAN_PATH=leanpath),timeout=600,command=[sysroot+'/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-o','objects/'+m.replace('.','/')+'.olean',src],source_revision=plan['sources'][m]['revision'],source_original_path=plan['sources'][m]['path'],deps_fingerprint=dict(ndr_manifest_sha256=plan['ndr_manifest_sha256'],plan_sha256=sha('plan.json')),expected_time='mechanical recompilation against authoritative NDR cohort; no source/proof changes')
 Path('objects/'+m.replace('.','/')).parent.mkdir(parents=True,exist_ok=True)
 cfgfile=f'attempt-{a}.json';Path(cfgfile).write_text(json.dumps(cfg,indent=2)+'\n')
 for retry in range(11):
  admission=B/f'admission-{a}-{retry}.json';log=B/f'admission-{a}-{retry}.log'
  # Admission and scope launch are in this same process; both JSON and exit must admit.
  with log.open('w') as out:r=subprocess.run(['python3',str(B.parent/'codex-pv-runjoin-20261026/reservation-existing.py'),str(admission)],stdout=out,stderr=subprocess.STDOUT)
  result=json.load(open(admission)) if admission.exists() else None
  if r.returncode==0 and result and result.get('allowed') is True:break
  if r.returncode==78 or (result and result.get('allowed') is False):
   Path(f'refusal-{a}-{retry}.json').write_text(json.dumps(dict(epoch=time.time(),exit=r.returncode,admission=result,compiler_started=False)))
   print('REFUSED',a,retry,flush=True)
   if retry==10:sys.exit(78)
   time.sleep(180);continue
  print('INFRASTRUCTURE STOP',a,log.read_text(),flush=True);sys.exit(1)
 command=['systemd-run','--user','--scope','--quiet',f'--unit=pv-evhc2-{a}','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(B/'S2W_lean_host.py'),cfgfile]
 print('START',a,m,flush=True)
 with Path(f'launch-{a}.log').open('w') as out:r=subprocess.run(command,stdout=out,stderr=subprocess.STDOUT)
 receipt=B/f'lean-{a}/receipt.json'
 if not receipt.exists():print('STOP missing receipt',a,Path(f'launch-{a}.log').read_text(),flush=True);sys.exit(1)
 v=json.load(open(receipt));print('DONE',a,m,v['exit_status'],v['wall_seconds'],v['peak_rss_kib'],flush=True)
 if r.returncode or v['exit_status'] or int(v['peak_rss_kib'] or 0)>7*1024*1024 or v['wall_seconds']>=600:
  Path('STOP.json').write_text(json.dumps(dict(attempt=a,module=m,receipt=str(receipt),reason='failure or mandatory resource review; no retry',launch_exit=r.returncode),indent=2)+'\n');sys.exit(1)
print('STAGE1 BUILDS COMPLETE',time.monotonic()-start,flush=True)
