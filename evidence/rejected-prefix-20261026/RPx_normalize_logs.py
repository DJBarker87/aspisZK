"""Keep byte-exact originals while removing diagnostic trailing spaces in display copies."""
from pathlib import Path
import json,re,hashlib,base64
E=Path(__file__).resolve().parent;out=E/'RPx_raw_log_bytes.json'
originals=json.loads(out.read_text()) if out.exists() else {}
for p in E.rglob('*.log'):
    data=p.read_bytes();fixed=re.sub(rb'[ \t]+(?=\r?$)',b'',data,flags=re.M)
    if fixed==data:continue
    key=str(p.relative_to(E))
    assert key not in originals
    originals[key]=dict(original_sha256=hashlib.sha256(data).hexdigest(),original_base64=base64.b64encode(data).decode(),display_sha256=hashlib.sha256(fixed).hexdigest())
    p.write_bytes(fixed)
out.write_text(json.dumps(originals,indent=2)+'\n')
print('Normalized display logs, exact originals preserved:',len(originals))
