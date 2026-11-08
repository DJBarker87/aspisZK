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
raw=json.dumps(dict(files=rows,deletions=0),indent=1).encode();(B/'NNS_CACHE_IMPORTS.json.xz').write_bytes(lzma.compress(raw));(B/'NNS_CACHE_IMPORTS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
print(json.dumps(dict(files=len(rows),bytes=sum(x['bytes']for x in rows))))
