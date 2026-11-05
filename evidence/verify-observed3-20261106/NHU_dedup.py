"""Store each immutable source snapshot once, retaining its original path via a symlink."""
from pathlib import Path
import hashlib,json,os
E=Path(__file__).resolve().parent;store=E/'NHU_INPUTS'/'sources';store.mkdir(parents=True,exist_ok=True);rows=[]
for d in sorted(E.glob('NHU_[KLE][0-9][0-9][0-9]/sources')):
 for p in sorted(d.rglob('*')):
  if not p.is_file():continue
  raw=p.read_bytes();sha=hashlib.sha256(raw).hexdigest();dest=store/(sha+'.txt')
  if dest.exists():assert dest.read_bytes()==raw
  else:dest.write_bytes(raw)
  if not p.is_symlink():p.unlink();p.symlink_to(os.path.relpath(dest,p.parent))
  rows.append(dict(path=str(p.relative_to(E)),sha256=sha,bytes=len(raw),stored=str(dest.relative_to(E))))
(E/'NHU_SOURCE_STORE.json').write_text(json.dumps(dict(status='PASS',paths=rows,unique_sources=len({r['sha256'] for r in rows}),uncompressed_path_bytes=sum(r['bytes'] for r in rows),unique_bytes=sum(p.stat().st_size for p in store.iterdir())),indent=1)+'\n')
print(json.dumps(dict(paths=len(rows),unique_sources=len({r['sha256'] for r in rows}))))
