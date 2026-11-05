from pathlib import Path
import json,base64,hashlib
B=Path(__file__).resolve().parent;S=B/'NHW_src';inputs=json.loads((B/'NHW_FROZEN_ADDITIONS.json').read_text())
for n,v in inputs.items():
 p=S/n;raw=base64.b64decode(v['data']);assert hashlib.sha256(raw).hexdigest()==v['sha256']
 assert not p.exists(),n
 p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(raw)
pins=json.loads((B/'NHW_SOURCE_PINS.json').read_text());pins.update({n:v['sha256'] for n,v in inputs.items()})
(B/'NHW_SOURCE_PINS.json').write_text(json.dumps(pins,indent=1)+'\n')
(B/'NHW_INPUT_REPAIR.json').write_text(json.dumps(dict(reason='NHR extraction payload omitted cfg(kani)-only frozen include inputs; copied frozen files discovered from NHS source pins',files={n:v['sha256'] for n,v in inputs.items()},bytes=sum(len(base64.b64decode(v['data'])) for v in inputs.values()),source_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'),indent=1)+'\n')
print((B/'NHW_INPUT_REPAIR.json').read_text())
