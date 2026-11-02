from pathlib import Path
import json,hashlib,time,sys
B=Path(__file__).resolve().parent
O=Path('/home/dombarker/project-offloads')
P=O/'codex-pv-bridge-20261101'
N=O/'codex-cx-reconcile-cache-20261028'
checks=[]; resolutions=[]; start=time.monotonic()
def sha(p):
 with Path(p).open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def check(p,h):
 p=Path(p);actual=sha(p);checks.append({'path':str(p),'expected':h,'actual':actual});assert actual==h,('HASH MISMATCH',str(p),h,actual)
try:
 ready=json.load(open(B/'READY.json'))
 check(P/'READY.json',sha(B/'READY.json'))
 target=ready['proposed_new_aggregation_target'];check(P/(target['module']+'.lean'),target['sha256'])
 for f,h in {'reservation_agg16.py':'d6d40da5e7cad196b15974eb96526f28073d20b2c24855303d69bc605ebcac0f','S2W_lean_host_agg16.py':'9b325ab05e4aea7c8a2c3499ccef5de11898fdcba38cb803fc6a85111ca3f1dd','S2W_run_host_agg16.py':'8165ccff93f7d9b6043f55bf641c30c95c5af0f86d28b6e1b1ffef3aa5ea7ff6'}.items():
  check(O/'codex-cx-fixture-cache-20261027'/f,h);check(B/f,h)
 cp=O/'codex-pv-evhc2-20261029/resume3/COHORT-MANIFEST.json'
 check(cp,ready['reconciled_cohort_manifest_sha256']);cohort=json.load(open(cp))
 check(B/'NDR_FINAL_COHORT_PINS.json',ready['authoritative_ndr_manifest_sha256']);ndr=json.load(open(B/'NDR_FINAL_COHORT_PINS.json'))
 assert cohort['authoritative_manifest_sha256']==ready['authoritative_ndr_manifest_sha256']
 roots=list(map(Path,ready['LEAN_PATH'].split(':')))
 def resolve(m):
  top=m.split('.')[0];r=next(r for r in roots if (r/top).is_dir() or (r/(top+'.olean')).is_file());return r/(m.replace('.','/')+'.olean')
 for e in ndr['entries']:
  check(e['object_path'],e['object_sha256'])
  if 'source_sha256' in e:
   source=N/(e['module'].replace('.','/')+'.lean')
   check(source,e['source_sha256'])
 for e in cohort['entries']:
  p=resolve(e['module']);assert p==Path(e['path']),('RESOLUTION MISMATCH',e['module'],str(p),e['path'])
  resolutions.append({'module':e['module'],'path':str(p),'sha256':e['sha256']})
  for f in [e]+e['companions']:check(f['path'],f['sha256'])
 active=json.load(open(B/'ACTIVE-OBJECT-PINS.json'))
 freeze=json.load(open(B/'HANDOFF-SOURCE-FREEZE.json'))['files']
 for f,h in active['files'].items():
  p=P/f;check(p,h);m=p.stem;assert resolve(m)==p
  rs=[json.load(open(q)) for q in sorted(P.glob('lean-*/receipt.json'))]
  rs=[r for r in rs if r.get('module')==m and r.get('exit_status')==0];assert rs,m
  r=rs[-1];source=P/(m+'.lean');hsrc=sha(source);assert hsrc in r['source_hashes'].values(),('ACTIVE SOURCE',m)
  check(source,hsrc)
  assert any(v['sha256']==hsrc and Path(f).stem==m for f,v in freeze.items()),('HANDOFF SOURCE',m)
  resolutions.append({'module':m,'path':str(p),'sha256':h})
  for suffix in ['.olean.server','.olean.private','.ir']:
   q=p.with_suffix(suffix)
   if q.exists():checks.append({'path':str(q),'actual':sha(q),'note':'active companion inventory; no prior companion hash in active pins'})
 for f,v in json.load(open(B/'NDR_FINAL_OUTPUT_PINS.json')).items():check(N/f,v['sha256'])
 # Guard against source proof/elaboration failures anywhere in the predecessor line.
 th=target['sha256']
 for d in [P,O/'codex-pv-evhc2-20261029',O/'codex-pv-evhc-20261029',B]:
  for p in d.rglob('receipt.json'):
   old=json.load(open(p))
   assert not(old.get('exit_status',0)!=0 and th in old.get('source_hashes',{}).values()),('UNCHANGED FAILED SOURCE',str(p))
 (B/'resolution.json').write_text(json.dumps({'LEAN_PATH':ready['LEAN_PATH'],'entries':resolutions},indent=2)+'\n')
 result={'status':'PASS','wall_seconds':time.monotonic()-start,'checks':len(checks),'resolved_modules':len(resolutions),'source_revision':'4e16fc7039e90c94bdf542e9c4c823f0955dee00'}
except Exception as e:
 result={'status':'STOP BEFORE ADMISSION','error':repr(e),'wall_seconds':time.monotonic()-start,'checks':len(checks)}
(B/'hash-checks.json').write_text(json.dumps(checks,indent=2)+'\n');(B/'verification.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result),flush=True)
sys.exit(0 if result['status']=='PASS' else 1)
