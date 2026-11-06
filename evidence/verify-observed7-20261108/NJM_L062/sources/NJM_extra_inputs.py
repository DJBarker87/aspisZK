from pathlib import Path
import json,lzma,hashlib,base64
B=Path(__file__).resolve().parent;S=B/'NJM_src'
raw=(B/'NJM_EXTRA_INPUTS.json').read_bytes();assert hashlib.sha256(raw).hexdigest()==(B/'NJM_EXTRA_INPUTS.json.sha256').read_text().strip()
pins=json.loads((B/'NJM_FROZEN_FILE_PINS.json').read_text())
for n,v in json.loads(raw).items():
 data=base64.b64decode(v);p=S/n
 if p.exists():assert p.read_bytes()==data,n
 else:p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data)
 pins[n]=hashlib.sha256(data).hexdigest()
(B/'NJM_FROZEN_FILE_PINS.json').write_text(json.dumps(pins,indent=2)+'\n')
print('NJM missing cfg(kani) source inputs restored from frozen revision')
