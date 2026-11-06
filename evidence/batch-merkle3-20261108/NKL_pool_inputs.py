"""Lossless large-input pooling by logical archive path, never host caches."""
from pathlib import Path
import hashlib,json,lzma
E=Path(__file__).resolve().parent;manifest=E/'NKL_POOLED_INPUTS.json'
refs=json.loads(manifest.read_text()) if manifest.exists() else {}
sha=lambda b:hashlib.sha256(b).hexdigest()
canonical={sha(p.read_bytes()):p for p in E.iterdir() if p.is_file() and p.stat().st_size>=1000000}
removed=0
for p in sorted(E.rglob('*.xz')):
 if p.parent==E or 'NKL_pool' in p.parts:continue
 sibling=p.with_name(p.name[:-3]+'.sha256')
 if not sibling.is_file():continue
 raw=lzma.decompress(p.read_bytes());digest=sha(raw)
 assert sibling.read_text().strip()==digest,p
 if len(raw)<1000000:continue
 name=str(p.relative_to(E))[:-3]
 if digest in canonical:
  target=canonical[digest];ref=dict(file=str(target.relative_to(E)),sha256=digest,bytes=len(raw))
 else:
  target=E/'NKL_pool'/(digest+'.xz');target.parent.mkdir(exist_ok=True)
  if not target.exists():target.write_bytes(lzma.compress(raw,preset=6))
  assert sha(lzma.decompress(target.read_bytes()))==digest
  ref=dict(pool=str(target.relative_to(E)),sha256=digest,bytes=len(raw))
 refs[name]=ref;p.unlink();sibling.unlink();removed+=1
manifest.write_text(json.dumps(refs,indent=2,sort_keys=True)+'\n')
print(f'NKL pooled {removed} repeated large snapshots; {len(refs)} logical inputs retained')
