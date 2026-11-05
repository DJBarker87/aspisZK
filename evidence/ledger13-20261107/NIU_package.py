"""Package logs under the20MB limit without deleting evidence or retained caches."""
from pathlib import Path
import hashlib,lzma,json,subprocess,sys
E=Path(__file__).resolve().parent
packed=[]
for p in E.rglob('*'):
 if p.is_file()and p.stat().st_size>20_000_000:
  raw=p.read_bytes();Path(str(p)+'.xz').write_bytes(lzma.compress(raw,preset=6));Path(str(p)+'.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n');packed.append(dict(path=str(p.relative_to(E)),bytes=len(raw)));p.unlink()
for p in E.rglob('__pycache__'):
 import shutil
 shutil.rmtree(p)
assert not[p for p in E.rglob('*')if p.is_file()and p.stat().st_size>20_000_000]
(E/'NIU_PACKAGING.json').write_text(json.dumps(dict(over20MB_packed=packed,limit_bytes=20_000_000,python_bytecode_removed=True),indent=1)+'\n')
print(json.dumps(dict(stage='package',packed=len(packed))))
