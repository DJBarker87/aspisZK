"""Read-only recovery of exact native inputs from submitted attempt snapshots."""
from NEO_remote import *
import lzma,hashlib
attempts=sorted(p.parent.name for p in E.glob('NEO_K*/receipt.json'))
for a in attempts:
 name=a+'_INPUTS.json'
 if (E/(name+'.xz')).exists():continue
 code=f'''from pathlib import Path
import json
b=Path({B!r});p=b/{a!r}/'sources'
print(json.dumps({{str(q.relative_to(p)):q.read_text() for q in p.rglob('*') if q.is_file()}},sort_keys=True,separators=(',',':')))
'''
 r=ssh(a+'_RECOVER','python3',code);assert r.returncode==0,r.stderr
 data=json.loads(r.stdout);rc=json.loads((E/a/'receipt.json').read_text())
 assert set(data)==set(rc['source_hashes']),(a,'missing snapshots')
 assert all(hashlib.sha256(text.encode()).hexdigest()==rc['source_hashes'][path] for path,text in data.items()),a
 raw=r.stdout.encode();blob=lzma.compress(raw,preset=6);assert len(blob)<20*1024**2
 (E/(name+'.xz')).write_bytes(blob);(E/(name+'.sha256')).write_text(hashlib.sha256(raw).hexdigest()+'  '+name+'\n')
 print(a,len(data),'inputs recovered',flush=True)
