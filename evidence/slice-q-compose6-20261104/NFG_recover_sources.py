"""Read-only recovery of original runner snapshots; never resubmits a job."""
from NFG_remote import *
import base64,hashlib,lzma,sys
for a in sys.argv[1:]:
 r=ssh(a,'python3',f'''from pathlib import Path
import json,lzma,base64,hashlib
b=Path({B!r});src=b/{a!r}/'sources';rc=json.loads((b/{a!r}/'receipt.json').read_text())
inputs={{str(p.relative_to(src)):p.read_text() for p in src.rglob('*') if p.is_file()}}
assert set(inputs)==set(rc['source_hashes'])
for n,s in inputs.items():assert hashlib.sha256(s.encode()).hexdigest()==rc['source_hashes'][n]
plain=json.dumps(inputs,sort_keys=True).encode();print(json.dumps(dict(data=base64.b64encode(lzma.compress(plain,preset=6)).decode(),sha256=hashlib.sha256(plain).hexdigest(),files=len(inputs))))
''');assert r.returncode==0,r.stderr
 d=json.loads(r.stdout);raw=base64.b64decode(d['data']);plain=lzma.decompress(raw);assert hashlib.sha256(plain).hexdigest()==d['sha256']
 (E/(a+'_INPUTS.json.xz')).write_bytes(raw);(E/(a+'_INPUTS.json.sha256')).write_text(d['sha256']+'\n')
 print(a,d['files'],'snapshot inputs recovered')
