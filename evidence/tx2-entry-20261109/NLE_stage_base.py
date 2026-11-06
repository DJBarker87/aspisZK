from pathlib import Path
import json,lzma,base64,hashlib
B=Path('/home/dombarker/project-offloads/codex-cx-tx2-entry-20261109');raw=lzma.decompress((B/'NLE_BASE.json.xz').read_bytes())
assert hashlib.sha256(raw).hexdigest()==(B/'NLE_BASE.json.sha256').read_text().strip()
for n,b in json.loads(raw).items():
 p=B/'NLE_src'/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(base64.b64decode(b))
print('NLE frozen base staged')
