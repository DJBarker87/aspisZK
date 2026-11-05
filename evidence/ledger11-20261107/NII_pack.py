"""Store repeated large snapshots once by uncompressed SHA; preserve source bytes."""
from pathlib import Path
import json,lzma,hashlib
E=Path(__file__).resolve().parent
for a in sorted(E.glob('NII_L[0-9][0-9][0-9]')):
 for p in a.rglob('*'):
  if not p.is_file()or '/sources/'not in str(p)or p.stat().st_size<10000 or p.name.endswith('.REFERENCE.json'):continue
  raw=p.read_bytes();h=hashlib.sha256(raw).hexdigest();base=E/'NII_pinned_inputs';base.mkdir(exist_ok=True)
  if (base/h).exists():q=base/h;encoding='raw';assert q.read_bytes()==raw
  else:
   q=base/(h+'.xz');encoding='xz'
   if q.exists():assert lzma.decompress(q.read_bytes())==raw
   else:q.write_bytes(lzma.compress(raw,preset=6))
  x=dict(original_path=str(p.relative_to(E)),sha256=h,bytes=len(raw),stored_once=str(q.relative_to(E)),encoding=encoding);Path(str(p)+'.REFERENCE.json').write_text(json.dumps(x,indent=1)+'\n');p.unlink()
for p in list(E.rglob('*')):
 if p.is_file()and p.stat().st_size>20_000_000:
  raw=p.read_bytes();Path(str(p)+'.xz').write_bytes(lzma.compress(raw,preset=6));Path(str(p)+'.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n');p.unlink()
rows=[json.loads(p.read_text())for p in E.glob('NII_L*/sources/**/*.REFERENCE.json')]
(E/'NII_PACK.json').write_text(json.dumps(dict(references=rows,rule='Large pinned inputs stored once by SHA256; original evidence bytes unchanged'),indent=1)+'\n');print(len(rows),'packed source references')
