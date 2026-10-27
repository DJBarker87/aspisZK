import json,hashlib
from RPx_attempt import E,R,B,ssh
pins=json.loads((R/'evidence/replay-tops3-20261027/RPv_retained-object-pins.json').read_text())
for l in (E/'RPx_overlay-additions.jsonl').read_text().splitlines():
 for path,x in json.loads(l)['artifacts'].items():
  for name in [path,x['target']]:pins[name]={k:x[k] for k in ['sha256','bytes']}
for f in E.glob('RPx_*/receipt.json'):
 d=json.loads(f.read_text())
 for rel,h in d['source_hashes'].items():pins[B+'/'+rel]=dict(sha256=h,bytes=(E/rel.split('/')[-1]).stat().st_size)
 for x in d['deps_fingerprint']['selected_objects'].values():pins[x['path']]={k:x[k] for k in ['sha256','bytes']}
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
r=ssh('python3 -',payload);(E/'RPx_seal.log').write_text(r.stdout+r.stderr);assert r.returncode==0,r.stderr
out=json.loads(r.stdout);(E/'RPx_seal.json').write_text(json.dumps(out,indent=2)+'\n');assert not out['errors'],out
(E/'RPx_retained-object-pins.json').write_text(json.dumps(pins,indent=2)+'\n');print(out)
