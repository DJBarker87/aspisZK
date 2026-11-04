"""Archive raw machine output byte-exactly; never alter evidence whitespace."""
from pathlib import Path
import lzma,hashlib,json
E=Path(__file__).resolve().parent
for p in E.rglob('*.log'):
 if not p.is_file():continue
 raw=p.read_bytes();q=p.with_name(p.name+'.xz');q.write_bytes(lzma.compress(raw,preset=6));p.with_name(p.name+'.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n');p.unlink()
for p in E.rglob('*'):
 if p.is_file() and p.stat().st_size>20*1024*1024:raise RuntimeError(str(p))
