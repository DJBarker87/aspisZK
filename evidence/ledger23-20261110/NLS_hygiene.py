"""Archive raw logs byte-for-byte; never normalize evidence contents."""
from pathlib import Path
import hashlib,lzma,json
E=Path(__file__).resolve().parent;count=0
for p in sorted(E.rglob('*')):
 if not p.is_file():continue
 if p.suffix!='.log'and p.stat().st_size<=20000000:continue
 b=p.read_bytes();Path(str(p)+'.xz').write_bytes(lzma.compress(b,preset=6));Path(str(p)+'.sha256').write_text(hashlib.sha256(b).hexdigest()+'\n');p.unlink();count+=1
assert not [p for p in E.rglob('*')if p.is_file()and p.stat().st_size>20000000]
print(json.dumps(dict(status='PASS',byte_preserving_archives_added=count,files_over20MB=0)))
