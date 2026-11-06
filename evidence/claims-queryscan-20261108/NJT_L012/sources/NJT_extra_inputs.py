from pathlib import Path
import json,lzma,hashlib,base64
B=Path(__file__).resolve().parent;S=B/'NJT_src'
p=Path('/home/dombarker/project-offloads/codex-cx-verify-observed7-20261108/NJM_EXTRA_INPUTS.json');raw=p.read_bytes();assert hashlib.sha256(raw).hexdigest()=='0a3887d917c42f2a8c141ec9a9751ef02174d58ebea90c235065c1f1bfd6ff4c'
pins=json.loads((B/'NJT_FROZEN_FILE_PINS.json').read_text())
for n,v in json.loads(raw).items():
 data=base64.b64decode(v);p=S/n
 if p.exists():assert p.read_bytes()==data,n
 else:p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data)
 pins[n]=hashlib.sha256(data).hexdigest()
(B/'NJT_FROZEN_FILE_PINS.json').write_text(json.dumps(pins,indent=2)+'\n')
print('NJM missing cfg(kani) source inputs restored from frozen revision')
