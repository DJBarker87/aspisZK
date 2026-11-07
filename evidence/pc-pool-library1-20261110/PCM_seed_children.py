"""Copy only retained Stream C module packets needed by the requested gate."""
from pathlib import Path
import json,subprocess,lzma,hashlib
E=Path(__file__).resolve().parent; rows=[]
for folder,pre,name in [('pc-helpers1-20261110','PCB','PCB_EXPORT_MANIFEST.json'),('pc-helpers2-20261110','PCG','PCG_EXPORT_MANIFEST.json'),('pc-deposit-children1-20261110','PCF','PCF_EXPORT.json'),('pc-deposit-children2-20261110','PCI','PCI_EXPORT.json'),('pc-terminal-children1-20261110','PCD','PCD_EXPORT.json')]:
 j=json.loads((E.parent/folder/name).read_text())
 for r in j.get('objects',j.get('files',j.get('copies',[]))):
  src=r.get('export_path',r.get('export',r.get('path')))
  if not src or not any(src.endswith(x) for x in ['.olean','.olean.private','.olean.server','.ir']):continue
  start=src.rfind('/'+pre+'_');assert start>=0,src
  relative=src[start+1:]
  rows.append(dict(source=src,relative=relative,sha256=r['sha256']))
B='/home/dombarker/project-offloads/codex-pc-pool-library1-cache-20261110'
code='''from pathlib import Path
import shutil,hashlib,json,lzma
b=Path(B);assert shutil.disk_usage(b).free>=40_000_000_000
out=[]
for r in rows:
 src=Path(r['source']);dst=b/'PCM_children'/r['relative'];dst.parent.mkdir(parents=True,exist_ok=True)
 assert hashlib.sha256(src.read_bytes()).hexdigest()==r['sha256'],str(src)
 if dst.exists():assert hashlib.sha256(dst.read_bytes()).hexdigest()==r['sha256']
 else:shutil.copy2(src,dst)
 out.append(dict(r,destination=str(dst),bytes=dst.stat().st_size))
p=b/'PCM_CHILD_IMPORTS.json';p.write_text(json.dumps(out))
print(json.dumps(dict(files=len(out),bytes=sum(r['bytes'] for r in out),sha256=hashlib.sha256(p.read_bytes()).hexdigest())))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','python3'],input='B='+repr(B)+'\nrows='+repr(rows)+'\n'+code,text=True,capture_output=True)
(E/'PCM_CHILD_COPY.log').write_text(r.stdout+r.stderr);assert r.returncode==0,r.stderr
(E/'PCM_CHILD_COPY.json').write_text(r.stdout)
# Download receipts without printing their payloads.
for remote in ['PCM_CHILD_IMPORTS.json','PCM_CONTEXT_IMPORTS.json.xz']:
 with (E/remote).open('wb') as f:
  r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','cat',B+'/'+remote],stdout=f,stderr=subprocess.PIPE)
 assert r.returncode==0,r.stderr
print('PCM retained children copied and all context hashes collected')
