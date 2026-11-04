"""Read-only dependency source capture for the remaining buffer rows."""
from pathlib import Path
import subprocess,json
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdcd4-20261029'
code='''from pathlib import Path
import json,hashlib
metadata=json.load(open('/home/dombarker/project-offloads/codex-pv-rdcd3-20261028/rdcd4-20261029/classify-project-encoder/metadata.json'));rows=[]
for crate in ['generic-array-0.14.7','block-buffer-0.10.4','digest-0.10.7']:
 name,version=crate.rsplit('-',1)
 found=[Path(p['manifest_path']).parent/'src' for p in metadata['packages'] if p['name']==name and p['version']==version];assert len(found)==1,(crate,found)
 for p in found[0].rglob('*.rs'):
  b=p.read_bytes();rows.append(dict(crate=crate,path=str(p),relative=str(p.relative_to(found[0])),sha256=hashlib.sha256(b).hexdigest(),text=b.decode()))
print(json.dumps(rows))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3','-'],input=code,text=True,capture_output=True);assert r.returncode==0,r.stderr
j=json.loads(r.stdout);(E/'buffer-dependency-sources.json').write_text(json.dumps(j,indent=2)+'\n');print('Read',len(j),'pinned dependency source files; no build or new row credit.')
