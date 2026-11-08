"""Retain exact selected closure and own objects; no deletion or shared writes."""
from pathlib import Path
import os,json,lzma,hashlib
B=Path.cwd();roots=os.environ['LEAN_PATH'].split(':')
loaded=[l.removeprefix('NNS_MODULE ') for l in (B/'NNS_L021/stdout.log').read_text().splitlines() if l.startswith('NNS_MODULE ')]
assert loaded
loaded=list(dict.fromkeys(loaded+['NNS_COMBINED_IMPORT']))
wanted={n.replace('.','/')+'.olean':n for n in loaded};selected={}
# Search only requested package subdirectories, never entire offload caches.
packages={n.split('.')[0] for n in loaded if '.' in n}
direct={r for r in wanted if '/' not in r}
for root in roots:
 p=Path(root)
 if not p.is_dir():continue
 for z in p.iterdir():
  if z.name in direct and z.is_file():selected.setdefault(z.name,z)
 for package in packages:
  q=p/package
  if not q.is_dir():continue
  for z in q.rglob('*.olean'):
   rel=str(z.relative_to(p))
   if rel in wanted:selected.setdefault(rel,z)
missing=sorted(set(wanted)-set(selected));assert not missing,missing
pins=[]
for rel,n in wanted.items():
 p=selected[rel]
 for z in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if z.is_file():pins.append(dict(module=n,path=str(z),sha256=hashlib.sha256(z.read_bytes()).hexdigest(),bytes=z.stat().st_size))
raw=json.dumps(dict(LEAN_PATH=roots,modules=loaded,selected_objects=pins,combined='NNS_L021',scope='focused cached composition; no cold release replay'),indent=1).encode()
(B/'NNS_CLOSURE_PINS.json.xz').write_bytes(lzma.compress(raw));(B/'NNS_CLOSURE_PINS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
own=[r for r in pins if r['module'].startswith('NNS_')]
assert len({r['module'] for r in own})==10
(B/'NNS_EXPORT.json').write_text(json.dumps(dict(object_directory=str(B/'NNS_objects_v2'),prepend=[str(B/'NNS_objects_v2'),str(B/'NNS_primary')],LEAN_PATH=roots,files=own,requested_roots_delivered=False,cache_retained=True,deletions=0),indent=1)+'\n')
print(json.dumps(dict(modules=len(loaded),selected_files=len(pins),own_modules=len({r['module'] for r in own}),retained=True,deletions=0)))
