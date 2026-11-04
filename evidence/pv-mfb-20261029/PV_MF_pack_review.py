"""Store bulky generated tables without committing files over the 20 MiB limit."""
from pathlib import Path
import hashlib,lzma
D=Path(__file__).resolve().parent
for name in ['rows9-input.json','candidate-traces.json','resolved-traces.json','exact-traces.json']:
 p=D/name
 if p.exists():
  raw=p.read_bytes();(D/(name+'.xz')).write_bytes(lzma.compress(raw,preset=6));(D/(name+'.sha256')).write_text(hashlib.sha256(raw).hexdigest()+'  '+name+'\n');p.unlink()
assert not [p for p in D.rglob('*') if p.is_file() and p.stat().st_size>20*1024*1024]
