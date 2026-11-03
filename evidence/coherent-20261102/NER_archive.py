"""Preserve large audit outputs as xz plus an uncompressed SHA-256 receipt."""
import hashlib,lzma,sys
from pathlib import Path
for pattern in sys.argv[1:]:
 for p in Path('.').glob(pattern):
  digest=hashlib.sha256()
  with p.open('rb') as src,lzma.open(str(p)+'.xz','wb',preset=6) as dst:
   while chunk:=src.read(1024*1024):digest.update(chunk);dst.write(chunk)
  Path(str(p)+'.sha256').write_text(digest.hexdigest()+'\n')
  print(p,p.stat().st_size,Path(str(p)+'.xz').stat().st_size,flush=True)
