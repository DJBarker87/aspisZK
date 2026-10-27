"""Read-only final input/output consistency; no compiler invocation."""
from pathlib import Path
import hashlib,json
from RPt_attempt import E,R,B,ssh
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
p=json.loads((E/'RPt_plan.json').read_text());rs=sorted([json.loads(f.read_text()) for f in E.glob('RPt_*/receipt.json')],key=lambda d:int(d['attempt'].split('_')[1]));errors=[];pins=json.loads((E/'RPt_inherited-object-pins.json').read_text())
expected={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
for d in rs:
 if d['limits']!=expected:errors.append({'scope':d['attempt'],'limits':d['limits']})
 if '-M7000' not in d['command']:errors.append({'lean_cap':d['attempt']})
 for x in d['deps_fingerprint']['selected_objects'].values():
  if x['path'] in pins and pins[x['path']]['sha256']!=x['sha256']:errors.append({'conflicting_pin':x['path']})
  pins[x['path']]=x
 for name,h in d['source_hashes'].items():
  if sha(E/Path(name).name)!=h:errors.append({'source_snapshot_drift':name})
for l in (E/'RPt_overlay-additions.jsonl').read_text().splitlines():
 for x in json.loads(l)['artifacts'].values():pins[x['target']]={'path':x['target'],'sha256':x['sha256'],'bytes':x['bytes']}
for r in p['rows']:
 if sha(R/r['source'])!=r['sha256']:errors.append({'snapshot_changed':r['module']})
 if sha(R/r['original_source'])!=r['original_sha256']:errors.append({'original_changed':r['original']})
for x in json.loads((E/'RPt_inherited-pins.json').read_text()):
 if sha(R/x['path'])!=x['sha256']:errors.append({'inherited_evidence_drift':x['path']})
for x in json.loads((E/'RPt_toolchain-pins.json').read_text()):
 if x['path'] in pins and pins[x['path']]['sha256']!=x['sha256']:errors.append({'toolchain_pin_conflict':x['path']})
 pins[x['path']]={k:x[k] for k in ['path','sha256','bytes']}
payload='''from pathlib import Path
import hashlib,json,subprocess
B=Path(%r);pins=json.loads(%r);errors=[]
for name,x in pins.items():
 p=Path(name)
 if not p.is_file():errors.append({'missing':name});continue
 h=hashlib.sha256(p.read_bytes()).hexdigest()
 if h!=x['sha256'] or p.stat().st_size!=x['bytes']:errors.append({'path':name,'actual':h,'expected':x})
print(json.dumps({'checked':len(pins),'errors':errors,'default_lake_object_directory_exists':(B/'.lake/build/lib/lean').exists(),'own_processes':[s for s in subprocess.check_output(['ps','-u','dombarker','-o','pid,args'],text=True).splitlines() if 'RPt' in s and 'python3 -' not in s]}))
'''%(B,json.dumps(pins))
r=ssh('python3 -',payload);(E/'RPt_final-host-check.log').write_text(r.stdout+r.stderr);assert r.returncode==0,r.stderr
host=json.loads(r.stdout);errors.extend(host['errors']);assert not host['default_lake_object_directory_exists']
nums=[int(d['attempt'].split('_')[1]) for d in rs];assert nums==list(range(1,len(rs)+1));assert len(rs)<=400
out={'attempts':len(rs),'source_revision':p['revision'],'checked_source_snapshots':len(p['rows']),'host':host,'errors':errors}
(E/'RPt_final-verification.json').write_text(json.dumps(out,indent=2)+'\n');print(out);assert not errors
(E/'RPt_final-object-pins.json').write_text(json.dumps(pins,indent=2)+'\n')
