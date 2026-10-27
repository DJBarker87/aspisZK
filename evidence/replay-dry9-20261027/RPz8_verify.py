"""Final read-only consistency gate for accepted replay inputs and outputs."""
import json,hashlib,subprocess
from pathlib import Path
from RPz8_attempt import E,R,B,ssh,collect
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rs=sorted([json.loads(f.read_text()) for f in E.glob('RPz8_*/receipt.json')],key=lambda d:int(d['attempt'].split('_')[1]));pins={};errors=[];sources=[]
for d in rs:
 for n,x in d['deps_fingerprint']['selected_objects'].items():
  if x['path'] in pins and pins[x['path']]!=x:errors.append({'conflicting_dependency_pin':x['path']})
  pins[x['path']]=x
 for name,h in d['source_hashes'].items():
  p=E/Path(name).name;actual=sha(p);sources.append({'attempt':d['attempt'],'source':str(p.relative_to(R)),'sha256':actual,'matches':actual==h})
  if actual!=h:errors.append({'source_snapshot_drift':name})
 expected={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 if d['limits']!=expected:errors.append({'scope_limit_mismatch':d['attempt'],'actual':d['limits']})
 if '-M7000' not in d['command']:errors.append({'lean_cap_mismatch':d['attempt']})
for line in (E/'RPz8_overlay-additions.jsonl').read_text().splitlines():
 for x in json.loads(line)['artifacts'].values():pins[x['target']]={'path':x['target'],'sha256':x['sha256'],'bytes':x['bytes']}
nums=[int(d['attempt'].split('_')[1]) for d in rs]
if nums!=list(range(1,len(rs)+1)):errors.append({'noncontiguous_attempt_numbers':nums})
if len(rs)>1500:errors.append({'budget_exceeded':len(rs)})
# Immutable inherited source/artifact evidence was checked at preflight. Verify
# its local pins and all newly selected inputs/outputs without another replay.
for x in json.loads((E/'RPz8_inherited-evidence-pins.json').read_text()):
 p=R/x['path']
 if sha(p)!=x['sha256'] or p.stat().st_size!=x['bytes']:errors.append({'inherited_evidence_drift':x['path']})
for name in ['RPz8_plan.json','RPz8_ARX-plan.json']:
 for r in json.loads((E/name).read_text())['rows']:
  src=R/r['source'];before=R/r.get('inherited_source',r.get('original_source'))
  if sha(src)!=r['sha256']:errors.append({'planned_source_drift':r['module']})
  expected=r.get('inherited_sha256',r.get('original_sha256'))
  if sha(before)!=expected:errors.append({'selected_inherited_source_drift':r['module']})
payload='''import json,hashlib,subprocess
from pathlib import Path
B=Path(%r);pins=json.loads(%r);errors=[]
for name,x in pins.items():
 p=Path(name)
 if not p.is_file():errors.append({'missing':name});continue
 actual=hashlib.sha256(p.read_bytes()).hexdigest()
 if actual!=x['sha256'] or p.stat().st_size!=x['bytes']:errors.append({'drift':name,'actual':actual,'expected':x})
out={'checked_artifacts':len(pins),'errors':errors,'default_lake_object_directory_exists':(B/'.lake/build/lib/lean').exists(),'own_process_snapshot':chr(10).join(line for line in subprocess.run(['ps','-u','dombarker','-o','pid,args'],capture_output=True,text=True).stdout.splitlines() if 'RPz8' in line)}
(B/'RPz8_final-host-check.json').write_text(json.dumps(out,indent=2)+'\\n');print(json.dumps({k:v for k,v in out.items() if k!='own_process_snapshot'}))
'''%(B,json.dumps(pins))
r=ssh('python3 -',payload);assert r.returncode==0,r.stderr;collect('RPz8_final-host-check.json');host=json.loads(r.stdout);errors.extend(host['errors'])
if host['default_lake_object_directory_exists']:errors.append({'unexpected_default_lake_object_directory':True})
summary={'attempts':len(rs),'passed':sum(d['exit_status']==0 for d in rs),'failed':sum(d['exit_status']!=0 for d in rs),'compiler_wall_seconds':sum(d['wall_seconds'] for d in rs),'peak_rss_kib':max(int(d['peak_rss_kib']) for d in rs),'swaps':sum(int(d['swaps']) for d in rs),'reservation_retries':sum(d['reservation_retries'] for d in rs),'source_snapshot_checks':sources,'host_checks':host,'inherited_host_check':'RPz8_inherited-host-check.json','errors':errors,'kani_runs':0,'lean_limit':1500}
(E/'RPz8_final-verification.json').write_text(json.dumps(summary,indent=2)+'\n');print({k:v for k,v in summary.items() if k not in ['source_snapshot_checks','host_checks']});assert not errors,errors
