#!/usr/bin/env python3
"""Read/cache inventory only. No compiler/build/solver or live cache mutation."""
from pathlib import Path
import hashlib,json,struct,tarfile,sys
W=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021/s6-sdk-first-cache-20261024');W.mkdir(exist_ok=True)
known=set(json.loads((W/'known.json').read_text()));base=Path('/home/dombarker/project-offloads/codex-cx-s2w-20261023');receipt=json.loads((base/'lean-109/receipt.json').read_text());roots=[Path(p) for p in receipt['env']['LEAN_PATH'].split(':')]
# Same bounded olean-header reader as the existing local pin-imports utility.
ns={};exec(compile((W/'header-reader.py').read_text(),'header-reader','exec'),ns);imports=ns['imports']
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();todo=['S2W_D189Consolidation'];seen={};common=[];members=[]
while todo:
 n=todo.pop()
 if n in seen:continue
 rel=Path(*n.split('.')).with_suffix('.olean');p=next((r/rel for r in roots if (r/rel).is_file()),None);assert p is not None,n
 row=dict(name=n,path=str(p),sha256=sha(p));seen[n]=row
 if n in known:
  common.append(row);continue
 row['imports']=imports(p);row['files']=[]
 for ext in ['.olean','.olean.server','.olean.private','.ir']:
  q=p.with_suffix(ext)
  if q.is_file():
   target=str(rel.with_suffix(ext));members.append((q,target));row['files'].append(dict(relative=target,path=str(q),sha256=sha(q)))
 src=p.with_suffix('.lean')
 if not src.is_file():src=base/'src'/Path(*n.split('.')).with_suffix('.lean')
 if src.is_file():
  target='sources/'+str(rel.with_suffix('.lean'));members.append((src,target));row['source']=dict(path=str(src),relative=target,sha256=sha(src))
 todo+=row['imports']
(W/'inventory.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',seed='S2W_D189Consolidation',source_receipt=str(base/'lean-109/receipt.json'),source_receipt_sha256=sha(base/'lean-109/receipt.json'),modules=[r for n,r in seen.items() if n not in known],common=common,qualification='Warm source/object recovery; stopping at already selected local module names. Common objects require compatibility assessment. Not a coherent release reconstruction.'),indent=2)+'\n')
with tarfile.open(W/'objects.tar.gz','w:gz') as t:
 for p,target in members:t.add(p,arcname=target,recursive=False)
for n in ['lean-106','lean-109','lean-110']:
 p=base/n/'receipt.json';(W/(n+'-receipt.json')).write_bytes(p.read_bytes())
print(json.dumps(dict(new_modules=len(seen)-len(common),common=len(common),transfer_bytes=(W/'objects.tar.gz').stat().st_size)))
