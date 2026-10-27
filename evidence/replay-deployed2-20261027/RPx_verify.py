from pathlib import Path
import json,hashlib
from RPx_attempt import E,R,ssh
pins=json.loads((R/'evidence/replay-tops3-20261027/RPv_retained-object-pins.json').read_text())
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
r=ssh('python3 -',payload);(E/'RPx_inherited-check.log').write_text(r.stdout+r.stderr);assert r.returncode==0,r.stderr
out=json.loads(r.stdout);(E/'RPx_inherited-check.json').write_text(json.dumps(out,indent=2)+'\n');assert not out['errors'],out
print(out)
