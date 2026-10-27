from pathlib import Path
import hashlib,json
from RPt_attempt import E,R,B,ssh
P=R/'evidence/replay-dry9-20261027';pins={}
for f in P.glob('RPz8_*/receipt.json'):
 d=json.loads(f.read_text())
 for x in d['deps_fingerprint']['selected_objects'].values():pins[x['path']]=x
for l in (P/'RPz8_overlay-additions.jsonl').read_text().splitlines():
 for x in json.loads(l)['artifacts'].values():pins[x['target']]={'path':x['target'],'sha256':x['sha256'],'bytes':x['bytes']}
for x in json.loads((P/'RPz8_cleanup.json').read_text())['removed_query_only_objects']:pins.pop(x['path'],None)
payload='''from pathlib import Path
import hashlib,json
pins=json.loads(%r);errors=[]
for name,x in pins.items():
 p=Path(name)
 if not p.is_file():errors.append({'missing':name});continue
 h=hashlib.sha256(p.read_bytes()).hexdigest()
 if h!=x['sha256'] or p.stat().st_size!=x['bytes']:errors.append({'path':name,'expected':x,'actual':h})
print(json.dumps({'checked':len(pins),'errors':errors}))
'''%json.dumps(pins)
r=ssh('python3 -',payload);(E/'RPt_inherited-host-check.log').write_text(r.stdout+r.stderr);assert r.returncode==0,r.stderr
out=json.loads(r.stdout);(E/'RPt_inherited-host-check.json').write_text(json.dumps(out,indent=2)+'\n');print(out);assert not out['errors']
(E/'RPt_inherited-object-pins.json').write_text(json.dumps(pins,indent=2)+'\n')
