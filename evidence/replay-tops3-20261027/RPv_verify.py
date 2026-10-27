from pathlib import Path
import json,hashlib
from RPv_attempt import E,R,B,ssh
pins=json.loads((R/'evidence/replay-tops2-20261027/RPu_retained-object-pins.json').read_text())
transition=json.loads((E/'RPv_reservation-tool-transition.json').read_text());pins[transition['path']]={k:transition[k] for k in ['sha256','bytes']}
for l in (E/'RPv_overlay-additions.jsonl').read_text().splitlines():
 d=json.loads(l)
 for path,x in d['artifacts'].items():
  pins[path]={'sha256':x['sha256'],'bytes':x['bytes']};pins[x['target']]={'sha256':x['sha256'],'bytes':x['bytes']}
for f in E.glob('RPv_*/receipt.json'):
 d=json.loads(f.read_text())
 for rel,h in d['source_hashes'].items():pins[B+'/'+rel]={'sha256':h,'bytes':(E/Path(rel).name).stat().st_size}
 for x in d['deps_fingerprint']['selected_objects'].values():pins[x['path']]={'sha256':x['sha256'],'bytes':x['bytes']}
payload='''from pathlib import Path
import json,hashlib
pins=json.loads(%r);errors=[]
for n,x in pins.items():
 p=Path(n)
 if not p.is_file():errors.append(dict(path=n,error='missing'));continue
 h=hashlib.sha256(p.read_bytes()).hexdigest()
 if h!=x['sha256'] or p.stat().st_size!=x['bytes']:errors.append(dict(path=n,error='mismatch',actual=h))
print(json.dumps(dict(checked=len(pins),errors=errors)))
'''%json.dumps(pins)
r=ssh('python3 -',payload);(E/'RPv_verification.log').write_text(r.stdout+r.stderr);assert r.returncode==0,r.stderr
out=json.loads(r.stdout);(E/'RPv_verification.json').write_text(json.dumps(out,indent=2)+'\n');assert not out['errors'],out
(E/'RPv_retained-object-pins.json').write_text(json.dumps(pins,indent=2)+'\n');print(out)
