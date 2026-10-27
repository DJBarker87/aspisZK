"""Read-only inherited artifact validation; no prover or build-tool changes."""
import json,hashlib
from pathlib import Path
from RPz8_attempt import E,R,B,ssh,collect
O=R/'evidence/replay-dry8-20261026';pins={}
for row in json.loads((O/'RPz7_overlay-base.json').read_text()).values():pins[row['target']]={'sha256':row['sha256'],'bytes':row['bytes']}
for line in (O/'RPz7_overlay-additions.jsonl').read_text().splitlines():
 for row in json.loads(line)['artifacts'].values():pins[row['target']]={'sha256':row['sha256'],'bytes':row['bytes']}
for row in json.loads((O/'RPz7_cleanup.json').read_text())['removed_query_only_objects']:pins.pop(row['path'],None)
payload='''import json,hashlib
from pathlib import Path
B=Path(%r);pins=json.loads(%r);errors=[]
for name,x in pins.items():
 p=Path(name)
 if not p.is_file():errors.append({'missing':name});continue
 actual=hashlib.sha256(p.read_bytes()).hexdigest()
 if actual!=x['sha256'] or p.stat().st_size!=x['bytes']:errors.append({'drift':name,'actual':actual,'expected':x})
trusted=json.loads((B/'RPz_trusted-base.json').read_text());known=[]
for name,x in trusted['artifacts'].items():
 p=Path(name)
 if not p.is_file():errors.append({'trusted_missing':name});continue
 actual=hashlib.sha256(p.read_bytes()).hexdigest()
 if actual!=x['sha256'] or p.stat().st_size!=x['bytes']:
  row={'trusted_drift':name,'actual':actual,'expected':x}
  if name=='/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py' and actual=='195657d75fd2a290c236f078fca4247929f214d4f693532ae1fb4d5edc34d893':known.append(row)
  else:errors.append(row)
out={'artifact_count':len(pins),'trusted_base_count':len(trusted['artifacts']),'known_nonlibrary_drift':known,'errors':errors,'qualification':'Inherited coherent objects rehashed read-only; no new compile credit'}
(B/'RPz8_inherited-host-check.json').write_text(json.dumps(out,indent=2)+'\\n');print(json.dumps(out))
'''%(B,json.dumps(pins))
r=ssh('python3 -',payload);assert r.returncode==0,r.stderr;collect('RPz8_inherited-host-check.json');print(r.stdout)
