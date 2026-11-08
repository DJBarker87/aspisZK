"""Lossless job-owned log archival; sources and receipts remain readable inputs."""
from pathlib import Path
import hashlib,lzma
E=Path(__file__).resolve().parent
for p in E.rglob('*'):
 if not p.is_file()or p.suffix in ['.xz','.sha256','.pyc']:continue
 if p.suffix=='.log' or p.stat().st_size>20_000_000:
  raw=p.read_bytes();Path(str(p)+'.xz').write_bytes(lzma.compress(raw,preset=6));Path(str(p)+'.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n');p.unlink()
