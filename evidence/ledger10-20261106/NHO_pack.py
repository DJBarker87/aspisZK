"""Store repeated large receipt inputs once by uncompressed SHA256."""
from pathlib import Path
import json,lzma,hashlib
E=Path(__file__).resolve().parent;rows=[]
for a in sorted(E.glob('NHO_L[0-9][0-9][0-9]')):
 for p in a.rglob('*'):
  if not p.is_file()or '/sources/'not in str(p)or p.stat().st_size<10000:continue
  raw=p.read_bytes();h=hashlib.sha256(raw).hexdigest();q=E/'NHO_pinned_inputs'/(h+'.xz');q.parent.mkdir(exist_ok=True)
  if q.exists():assert hashlib.sha256(lzma.decompress(q.read_bytes())).hexdigest()==h
  else:q.write_bytes(lzma.compress(raw,preset=6))
  x=dict(original_path=str(p.relative_to(E)),sha256=h,bytes=len(raw),stored_once=str(q.relative_to(E)),encoding='xz');Path(str(p)+'.REFERENCE.json').write_text(json.dumps(x,indent=1)+'\n');p.unlink();rows.append(x)
# Rule12: compress every other over20MB file and retain its raw SHA.
for p in E.rglob('*'):
 if p.is_file()and p.stat().st_size>20_000_000:
  raw=p.read_bytes();Path(str(p)+'.xz').write_bytes(lzma.compress(raw,preset=6));Path(str(p)+'.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n');p.unlink()
(E/'NHO_PACK.json').write_text(json.dumps(dict(references=rows,rule='Large pinned inputs stored once by SHA256; every reference remains resolvable'),indent=1)+'\n')
print(len(rows),'packed source references')
