"""Fresh cross-job ID collision scan; read-only, no reservation or build."""
from run import H
from pathlib import Path
import re,os,json,time,sys
ids=sys.argv[1:];assert ids
found=[]
for base,dirs,files in os.walk(H.parent):
 if Path(base)==H:dirs[:]=[];continue
 depth=len(Path(base).relative_to(H.parent).parts)
 if depth>=5:dirs[:]=[]
 dirs[:]=[d for d in dirs if d not in {'target','sbf-target','charon-target','node_modules','.git','source','sources','.lake','objects','lean-objects','lean','generated','src','rebuild-objects'}]
 for name in dirs+files:
  if any(re.search(r'(?<![A-Za-z0-9])'+re.escape(v)+r'(?![A-Za-z0-9])',name)for v in ids):found.append(str(Path(base)/name))
 for n in files:
  if n=='sent.txt':
   for line in (Path(base)/n).read_text().splitlines():
    f=line.split()
    if len(f)>2 and f[2]in ids:found.append(str(Path(base)/n)+':'+line)
for ident in ids:
 assert not any((H/'resume17').glob('K'+ident+'*'))
x=dict(epoch=time.time(),ids=ids,collisions=found)
p=H/'resume17/ID-SCAN-D542.json';p.write_text(json.dumps(x,indent=2)+'\n');print(json.dumps(x));assert not found
