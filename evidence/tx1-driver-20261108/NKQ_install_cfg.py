from pathlib import Path
import json,base64,hashlib
B=Path(__file__).resolve().parent;S=B/'NKQ_src';x=json.loads((B/'NKQ_CFG_INPUTS.json').read_text());pins=json.loads((B/'NKQ_FROZEN_FILE_PINS.json').read_text())
for n,r in x['files'].items():
 p=S/n;p.parent.mkdir(parents=True,exist_ok=True);raw=base64.b64decode(r['base64']);assert hashlib.sha256(raw).hexdigest()==r['sha256']
 if p.exists():assert p.read_bytes()==raw
 else:p.write_bytes(raw)
 pins[n]=r['sha256']
(B/'NKQ_FROZEN_FILE_PINS.json').write_text(json.dumps(pins,indent=2));print('Frozen cfg-only path inputs installed and pinned; no crate source changed')
