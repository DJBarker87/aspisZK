from NMV_transport import *
raw=(E/'NMV_EXTRA_FROZEN.json').read_text()
r=ssh('python3',f'''from pathlib import Path
import json,base64,hashlib
b=Path({B!r});pins={{}}
for n,v in json.loads({raw!r}).items():
 p=b/'NMV_src'/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(base64.b64decode(v));pins[n]=hashlib.sha256(p.read_bytes()).hexdigest()
(b/'NMV_EXTRA_PINS.json').write_text(json.dumps(pins));print(json.dumps(pins))
''');assert r.returncode==0,r.stderr
(E/'NMV_EXTRA_PINS.json').write_text(r.stdout)
