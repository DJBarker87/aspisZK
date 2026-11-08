from pathlib import Path
import json,hashlib,shutil,lzma
B=Path.cwd();cfg=json.loads((B/'NNS_SEED_CONFIG.json').read_text());rows=[]
for root in cfg['exports']:
 p=Path(root)
 assert p.is_dir(),root
 for src in sorted(p.glob('*.olean')):
  dest=B/'NNS_seed'/src.name
  if dest.exists():continue
  for s,d in [(src,dest),(Path(str(src)+'.private'),Path(str(dest)+'.private')),(Path(str(src)+'.server'),Path(str(dest)+'.server')),(src.with_suffix('.ir'),dest.with_suffix('.ir'))]:
   if not s.exists():continue
   d.parent.mkdir(exist_ok=True);shutil.copy2(s,d)
   h=hashlib.sha256(s.read_bytes()).hexdigest();assert hashlib.sha256(d.read_bytes()).hexdigest()==h
   rows.append(dict(path=str(s),destination=str(d),sha256=h,bytes=s.stat().st_size))
# Aeneas namespace objects must be colocated with the selected root module.
for stem in ['Aeneas','AeneasMeta']:
 target=B/'NNS_seed'/(stem+'.olean')
 if not target.exists():continue
 root=next(Path(r) for r in cfg['paths'] if (Path(r)/(stem+'.olean')).is_file() and hashlib.sha256((Path(r)/(stem+'.olean')).read_bytes()).hexdigest()==hashlib.sha256(target.read_bytes()).hexdigest() and (Path(r)/stem).is_dir())
 for src in sorted((root/stem).rglob('*')):
  if not src.is_file():continue
  if not any(str(src).endswith(s) for s in ['.olean','.olean.private','.olean.server','.ir']):continue
  dest=B/'NNS_seed'/src.relative_to(root)
  dest.parent.mkdir(parents=True,exist_ok=True)
  if dest.exists():assert hashlib.sha256(dest.read_bytes()).hexdigest()==hashlib.sha256(src.read_bytes()).hexdigest()
  else:shutil.copy2(src,dest)
  rows.append(dict(path=str(src),destination=str(dest),sha256=hashlib.sha256(src.read_bytes()).hexdigest(),bytes=src.stat().st_size))
previous=B/'NNS_CACHE_IMPORTS.json.xz'
if previous.exists():rows=json.loads(lzma.decompress(previous.read_bytes()))['files']+rows
raw=json.dumps(dict(files=rows,deletions=0),indent=1).encode();previous.write_bytes(lzma.compress(raw));(B/'NNS_CACHE_IMPORTS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
print(json.dumps(dict(files=len(rows),bytes=sum(x['bytes']for x in rows))))
