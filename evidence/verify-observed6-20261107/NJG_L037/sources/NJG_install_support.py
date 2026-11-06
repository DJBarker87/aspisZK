from pathlib import Path
import json,base64,hashlib
B=Path(__file__).resolve().parent;S=B/'NJG_src';x=json.loads((B/'NJG_KANI_SUPPORT.json').read_text());pins=json.loads((B/'NJG_FROZEN_FILE_PINS.json').read_text())
for n,v in x['files'].items():
 b=base64.b64decode(v['base64']);assert hashlib.sha256(b).hexdigest()==v['sha256'];p=S/n;p.parent.mkdir(parents=True,exist_ok=True);assert not p.exists() or p.read_bytes()==b;p.write_bytes(b);pins[n]=v['sha256']
(B/'NJG_FROZEN_FILE_PINS.json').write_text(json.dumps(pins));print('NJG missing unchanged cfg(kani) support installed with frozen hashes')
