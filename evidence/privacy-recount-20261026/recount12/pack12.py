"""Compact duplicate input snapshots; originals remain committed Git blobs."""
from pathlib import Path
import json,gzip,lzma,hashlib,base64,subprocess,shutil
P=Path(__file__).resolve().parent
m=json.loads((P/'manifest.json').read_text());trees={};bundles={};current={};size=0;n=0
(P/'bundles').mkdir(exist_ok=True)
def flush():
 global current,size,n
 if not current:return
 path='bundles/inputs-%02d.json.xz'%n;(P/path).write_bytes(lzma.compress(json.dumps(current,separators=(',',':')).encode()));
 for key in current:bundles[key]=path
 current={};size=0;n+=1
for x in m:
 rev=x['revision']
 if rev not in trees:
  data=subprocess.check_output(['git','ls-tree','-r',rev]).decode().splitlines();trees[rev]={a.split('\t',1)[1]:a.split()[2] for a in data}
 x['blob']=trees[rev][x['path']]
 snap=x.get('snapshot');key=x['sha256']
 keep=x['bytes']<=200000 or (x['bytes']<=2000000 and (x['path'].endswith('.lean') or '/D637/' in x['path']))
 if keep and key not in bundles and key not in current:
  b=gzip.decompress((P/snap).read_bytes())
  assert hashlib.sha256(b).hexdigest()==key
  try:v={'encoding':'utf8','data':b.decode()}
  except UnicodeDecodeError:v={'encoding':'base64','data':base64.b64encode(b).decode()}
  current[key]=v;size+=len(b)
  if size>8000000:flush()
 x.pop('snapshot',None);x.pop('snapshot_key',None)
 x['storage']='compact snapshot plus committed Git blob' if keep else 'immutable committed Git blob (large duplicate inventory not copied)'
flush()
for x in m:
 if x['sha256'] in bundles:x.update(snapshot=bundles[x['sha256']],snapshot_key=x['sha256'])
(P/'manifest.json').write_text(json.dumps(m,indent=1)+'\n')
# Delete only this recount's duplicate source snapshot scratch, never keys.
shutil.rmtree(P/'objects')
print('manifest entries',len(m),'bundles',n,'bytes',sum(p.stat().st_size for p in P.rglob('*') if p.is_file()))
