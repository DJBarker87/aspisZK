"""Read-only SHA audit of the two committed import cohorts; never launches Lean."""
from pathlib import Path
import json, hashlib, time, subprocess
B=Path('/home/dombarker/project-offloads/codex-pv-evhc-20261029')
def sha(p):
 h=hashlib.sha256()
 with Path(p).open('rb') as f:
  for block in iter(lambda:f.read(1024*1024),b''):h.update(block)
 return h.hexdigest()
start=time.monotonic(); rows=[]
for cohort,filename,key in [('evh','evh-cohort-pins.json',None),('ndr','NDR_FINAL_COHORT_PINS.json','entries')]:
 data=json.loads((B/filename).read_text()); data=data[key] if key else data
 for r in data:
  path=r.get('object_path',r.get('path')); expected=r.get('object_sha256',r.get('sha256'))
  try:actual=sha(path); error=None
  except OSError as e:actual=None;error=str(e)
  rows.append(dict(cohort=cohort,module=r['module'],path=path,expected=expected,actual=actual,match=actual==expected,error=error))
ndr=B.parent/'codex-cx-reconcile-cache-20261028'
for f,pin in json.loads((B/'NDR_FINAL_OUTPUT_PINS.json').read_text()).items():
 path=ndr/f;actual=sha(path);rows.append(dict(cohort='ndr-output',module=f,path=str(path),expected=pin['sha256'],actual=actual,match=actual==pin['sha256']))
runner=B.parent/'codex-cx-fixture-cache-20261027'
runners={f:sha(runner/f) for f in ['reservation_agg16.py','S2W_lean_host_agg16.py','S2W_run_host_agg16.py']}
lean=Path('/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
x=dict(status='HASH AUDIT ONLY; NO COMPILER LAUNCHED',wall_seconds=time.monotonic()-start,checked=len(rows),mismatches=[r for r in rows if not r['match']],objects=rows,runners=runners,lean_binary_sha256=sha(lean))
(B/'host-hash-audit.json').write_text(json.dumps(x,indent=2)+'\n')
print(json.dumps({k:v for k,v in x.items() if k!='objects'},indent=2))
