"""Read-only pin of the library objects resolved by the exact Lean search path."""
from pathlib import Path
import hashlib,json,sys
paths=sys.argv[1].split(':')
keys={'Aeneas.olean'}
for root in paths:
 p=Path(root)/'Aeneas'
 if p.is_dir(): keys.update(str(q.relative_to(root)) for q in p.rglob('*.olean'))
chosen={}
for key in sorted(keys):
 p=next((Path(root)/key for root in paths if (Path(root)/key).is_file()),None)
 assert p is not None,key
 for q in [p,Path(str(p)+'.server'),Path(str(p)+'.private'),p.with_suffix('.ir')]:
  if q.is_file():chosen[str(q)]=dict(sha256=hashlib.sha256(q.read_bytes()).hexdigest(),bytes=q.stat().st_size)
print(json.dumps(chosen,indent=2))
