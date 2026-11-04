"""Store receipt inputs once, with content-preserving relative symlinks."""
from pathlib import Path
import hashlib,json,os
E=Path(__file__).resolve().parent;blob=E/'NFT_inputs';blob.mkdir(exist_ok=True);rows={}
for folder in sorted(E.glob('NFT_[KLE][0-9][0-9][0-9]/sources')):
 for p in sorted(folder.rglob('*')):
  if not p.is_file()or p.is_symlink()or p.stat().st_size<4096:continue
  raw=p.read_bytes();h=hashlib.sha256(raw).hexdigest();q=blob/(h+'.txt')
  if not q.exists():q.write_bytes(raw)
  assert q.read_bytes()==raw
  rel=os.path.relpath(q,p.parent);p.unlink();p.symlink_to(rel);assert hashlib.sha256(p.read_bytes()).hexdigest()==h
  rows[str(p.relative_to(E))]=dict(sha256=h,bytes=len(raw),blob=str(q.relative_to(E)))
old=E/'NFT_INPUT_ALIASES.json'
if old.exists():rows=json.loads(old.read_text())|rows
old.write_text(json.dumps(rows,indent=1)+'\n');print(len(rows),'content-checked input aliases')
