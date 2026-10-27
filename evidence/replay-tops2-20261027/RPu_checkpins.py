from pathlib import Path
import hashlib,json
from RPu_attempt import E,R,B,ssh
pins=json.loads((R/'evidence/replay-tops1-20261027/RPt_retained-object-pins.json').read_text())
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
r=ssh('python3 -',payload);(E/'RPu_inherited-host-check.log').write_text(r.stdout+r.stderr);assert r.returncode==0,r.stderr
out=json.loads(r.stdout);(E/'RPu_inherited-host-check.json').write_text(json.dumps(out,indent=2)+'\n');print(out);assert not out['errors']
(E/'RPu_inherited-object-pins.json').write_text(json.dumps(pins,indent=2)+'\n')
