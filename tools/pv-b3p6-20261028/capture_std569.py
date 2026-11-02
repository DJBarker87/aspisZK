"""Read-only source capture and body-token parity for the extracted nth helper."""
from pathlib import Path
import subprocess,json,hashlib,lzma,re
R=Path('evidence/pv-b3p6-20261028/resume18');O=R/'std569-source';O.mkdir(exist_ok=True)
code='''from pathlib import Path
import json,hashlib
names=['slice/iter/macros.rs','ops/index_range.rs']
versions=['1.94.1','nightly-2026-06-01'];out=[]
for v in versions:
 root=Path('/home/dombarker/.rustup/toolchains')/(v+'-x86_64-unknown-linux-gnu')/'lib/rustlib/src/rust/library/core/src'
 for name in names:
  p=root/name;b=p.read_bytes();out.append(dict(version=v,name=name,path=str(p),sha256=hashlib.sha256(b).hexdigest(),text=b.decode()))
print(json.dumps(out))
'''
rows=json.loads(subprocess.check_output(['ssh','dombarker@100.108.41.90','python3','-'],input=code,text=True))
manifest=[];sources={}
for r in rows:
 b=r.pop('text').encode();assert hashlib.sha256(b).hexdigest()==r['sha256'];p=O/r['version']/(r['name']+'.xz');p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(lzma.compress(b,preset=6));r['local_path']=str(p);r['bytes']=len(b);manifest.append(r);sources[(r['version'],r['name'])]=b.decode()
(R/'STD-SOURCE-CAPTURE-D569.json').write_text(json.dumps(manifest,indent=2)+'\n');print('captured',len(manifest),'source files')
