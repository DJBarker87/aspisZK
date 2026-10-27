"""Read-only final consistency checks; no Lean invocation or launcher changes."""
from pathlib import Path
import json,hashlib,subprocess,collections
from RPz7_attempt import E,R,B,ssh,collect
h=lambda b:hashlib.sha256(b).hexdigest()
rs=[json.loads(f.read_text()) for f in sorted(E.glob('RPz7_*/receipt.json'))]
errors=[];pins={};sources=[]
for d in rs:
 for n,x in d['deps_fingerprint']['selected_objects'].items():
  if x['path'] in pins and pins[x['path']]!=x:errors.append({'conflicting_dependency_pin':x['path']})
  pins[x['path']]=x
 for rel,digest in d['source_hashes'].items():
  src=E/Path(rel).name
  sources.append({'attempt':d['attempt'],'source':str(src.relative_to(R)),'expected':digest,'actual':h(src.read_bytes()),'matches':h(src.read_bytes())==digest})
  if not sources[-1]['matches']:errors.append(sources[-1])
for row in json.loads((E/'RPz7_overlay-base.json').read_text()).values():
 x={'path':row['target'],'sha256':row['sha256'],'bytes':row['bytes']}
 if x['path'] in pins and pins[x['path']]!=x:errors.append({'conflicting_base_pin':x['path']})
 pins[x['path']]=x
for line in (E/'RPz7_overlay-additions.jsonl').read_text().splitlines():
 for row in json.loads(line)['artifacts'].values():
  x={'path':row['target'],'sha256':row['sha256'],'bytes':row['bytes']};pins[x['path']]=x
if (E/'RPz7_cleanup.json').exists():
 for item in json.loads((E/'RPz7_cleanup.json').read_text())['removed_query_only_objects']:
  pins.pop(item['path'],None)
payload="""from pathlib import Path
import json,hashlib
B=Path(%r);pins=json.loads(%r);errors=[];checked=0
for name,x in pins.items():
 p=Path(name)
 if not p.is_file():errors.append({'missing':name});continue
 digest=hashlib.sha256(p.read_bytes()).hexdigest();checked+=1
 if digest!=x['sha256'] or p.stat().st_size!=x['bytes']:errors.append({'drift':name,'actual':digest,'expected':x})
trusted=json.loads((B/'RPz_trusted-base.json').read_text());trusted_checked=0;inherited_nonlibrary_drift=[]
for name,x in trusted['artifacts'].items():
 p=Path(name)
 if not p.is_file():errors.append({'trusted_missing':name});continue
 digest=hashlib.sha256(p.read_bytes()).hexdigest();trusted_checked+=1
 if digest!=x['sha256'] or p.stat().st_size!=x['bytes']:
  row={'trusted_drift':name,'actual':digest,'expected':x,'actual_bytes':p.stat().st_size}
  if name=='/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py' and digest=='195657d75fd2a290c236f078fca4247929f214d4f693532ae1fb4d5edc34d893' and x['sha256']=='f5b8318a7cdb5e03e5221a2e3c43c274fc0fe499afc53f2b6a091e2d4bd27180' and p.stat().st_size==2451:inherited_nonlibrary_drift.append(row)
  else:errors.append(row)
out={'checked_artifacts':checked,'trusted_base_checked':trusted_checked,'inherited_nonlibrary_drift':inherited_nonlibrary_drift,'trusted_base_manifest_sha256':hashlib.sha256((B/'RPz_trusted-base.json').read_bytes()).hexdigest(),'errors':errors,'own_runner_processes':'queried separately','default_lake_object_directory_exists':(B/'.lake/build/lib/lean').exists(),'qualification':'Hashes of accepted outputs, direct predecessor inputs and retained view; no fresh compilation claim for trusted library base.'}
(B/'RPz7_host-validation.json').write_text(json.dumps(out,indent=2)+'\\n')
print(json.dumps(out))
"""%(B,json.dumps(pins))
r=ssh('python3 -',payload)
if r.returncode:raise SystemExit('STOP final hash inspection: '+r.stderr)
collect('RPz7_host-validation.json');host=json.loads(r.stdout);errors+=host['errors']
original=json.loads((R/'evidence/replay-dry6-20261026/RPz5_source-plan.json').read_text())
checks=[]
for m in original['order']:
 x=original['modules'][m];actual=h((R/x['source']).read_bytes());checks.append({'module':m,'matches':actual==x['sha256']})
 if actual!=x['sha256']:errors.append({'original_source_drift':m})
selection=json.loads((E/'RPz7_plan.json').read_text());union=json.loads((R/'evidence/replay-dry6-20261026/RPz5_tx1-probe-source-plan.json').read_text());reuse_sources=[]
for m,view in selection['reuse'].items():
 x=union['modules'][m] if view=='RPz5_union_overlay' else original['modules'][m]
 actual=h((R/x['source']).read_bytes());row={'module':m,'view':view,'selected_source':x['source'],'expected_sha256':x['sha256'],'actual_sha256':actual,'matches':actual==x['sha256']};reuse_sources.append(row)
 if not row['matches']:errors.append({'selected_reused_source_drift':row})
nums=sorted(int(d['attempt'].split('_')[1]) for d in rs)
if nums!=list(range(1,1500-1)):errors.append({'attempt_numbers':nums,'expected':'1..1498'})
summary={'attempts':len(rs),'passes':sum(d['exit_status']==0 for d in rs),'failures':[{'attempt':d['attempt'],'module':d['module'],'exit':d['exit_status']} for d in rs if d['exit_status']],'compiler_wall_seconds':sum(d['wall_seconds'] for d in rs),'peak_rss_kib':max(int(d['peak_rss_kib']) for d in rs),'swaps':sum(int(d['swaps']) for d in rs),'source_snapshot_checks':sources,'original_planning_source_checks':len(checks),'selected_reused_source_checks':reuse_sources,'host_checks':host,'errors':errors,'budget_limit':1498,'kani_runs':0}
(E/'RPz7_final-verification.json').write_text(json.dumps(summary,indent=2)+'\n')
print({k:v for k,v in summary.items() if k not in ['source_snapshot_checks','host_checks','selected_reused_source_checks']})
assert not errors
