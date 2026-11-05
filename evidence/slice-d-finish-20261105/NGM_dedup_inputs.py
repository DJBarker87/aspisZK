"""Retain every attempt input at its original path, backed once by SHA256.
Only NGM-owned local evidence is changed. Symlink targets are relative and
stay within this packet, so a checkout remains self-contained.
"""
from pathlib import Path
import hashlib,json,os
E=Path(__file__).resolve().parent;store=E/'NGM_INPUTS';store.mkdir(exist_ok=True);rows=[]
for directory in sorted(E.glob('NGM_*/sources')):
 for p in sorted(directory.rglob('*')):
  if not p.is_file():continue
  data=p.read_bytes();digest=hashlib.sha256(data).hexdigest();target=store/digest
  if target.exists():assert target.read_bytes()==data
  else:target.write_bytes(data)
  assert len(data)<=20*1024*1024
  rows.append(dict(path=str(p.relative_to(E)),sha256=digest,bytes=len(data),stored=str(target.relative_to(E))))
  if not p.is_symlink():p.unlink();p.symlink_to(os.path.relpath(target,p.parent))
(E/'NGM_INPUT_INDEX.json').write_text(json.dumps(dict(format='relative symlink CAS; uncompressed bytes SHA256',inputs=rows,unique_files=len(set(r['sha256']for r in rows)),unique_bytes=sum(p.stat().st_size for p in store.iterdir())),indent=1)+'\n')
print(json.dumps(dict(inputs=len(rows),unique_files=len(set(r['sha256']for r in rows)),unique_bytes=sum(p.stat().st_size for p in store.iterdir()))))
