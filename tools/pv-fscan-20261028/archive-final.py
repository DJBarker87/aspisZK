from pathlib import Path
import json,hashlib,lzma
D=Path('/home/dombarker/project-offloads/codex-pv-fscan-20261028');B=D/'mir-blobs';B.mkdir(exist_ok=True);rows=[]
allowed=['libraries-charon','libraries-client194-exact','libraries-client194-dev-exact','libraries-deployed','libraries-dev','libraries-default']
for p in sorted(D.glob('*/crate.mir')):
 b=p.read_bytes();z=p.with_suffix('.mir.xz')
 if not z.exists():z.write_bytes(lzma.compress(b,preset=6))
 rows.append(dict(path=str(p.relative_to(D)),sha256=hashlib.sha256(b).hexdigest(),size=len(b),compressed=str(z.relative_to(D))))
for n in allowed:
 for p in sorted((D/n).glob('*.mir')):
  b=p.read_bytes();h=hashlib.sha256(b).hexdigest();z=B/(h+'.mir.xz')
  if not z.exists():z.write_bytes(lzma.compress(b,preset=6))
  rows.append(dict(path=str(p.relative_to(D)),sha256=h,size=len(b),compressed=str(z.relative_to(D))))
for p in D.glob('libraries-*/metadata.json'):
 b=p.read_bytes();p.with_suffix('.json.xz').write_bytes(lzma.compress(b,preset=6));p.with_suffix('.json.sha256').write_text(hashlib.sha256(b).hexdigest()+'\n')
(D/'dump-manifest.json').write_text(json.dumps(rows,indent=2));print('MIR snapshots',len(rows),'unique library blobs',len(list(B.glob('*.xz'))),'compressed bytes',sum(p.stat().st_size for p in B.glob('*.xz')))
