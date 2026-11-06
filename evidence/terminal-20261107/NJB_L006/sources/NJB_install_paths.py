from pathlib import Path
import json,base64,hashlib
b=Path(__file__).resolve().parent;s=b/'NJB_src';x=json.loads((b/'NJB_EXTRA_INPUTS.json').read_text())
for q,v in x.items():
 p=s/q;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(base64.b64decode(v,validate=True))
print('frozen literal path closure restored: '+str(len(x))+' files')
