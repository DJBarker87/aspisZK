"""Read-only pins for existing own outputs, with current-source provenance."""
from NFB_remote import *
import hashlib
assert not (E/'NFB_ACTIVE.json').exists()
g=json.loads((E/'NFB_GENERATED.json').read_text());last={}
for p in sorted(E.glob('NFB_L*/receipt.json')):
 r=json.loads(p.read_text());last[r['module']]=r
selected=[]
for m,r in last.items():
 if r['exit_status']!=0:continue
 rel=m.replace('.','/')+'.lean';p=E/(g[m]['path'] if m in g else rel)
 assert hashlib.sha256(p.read_bytes()).hexdigest()==r['source_hashes'][rel]
 selected.append(dict(attempt=r['attempt'],module=m,source_sha256=r['source_hashes'][rel],path=B+'/'+m.replace('.','/')+'.olean'))
r=ssh('NFB_OBJECT_PIN','python3',f'''from pathlib import Path
import json,hashlib
out=[]
for rec in {selected!r}:
 p=Path(rec['path']);out.append(dict(rec,sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size))
print(json.dumps(out))
''');assert r.returncode==0,r.stderr
for rec in json.loads(r.stdout):(E/rec['attempt']/'object.json').write_text(json.dumps(rec,indent=1)+'\n')
print('Pinned',len(selected),'own current objects; no compile or mutation on host')
