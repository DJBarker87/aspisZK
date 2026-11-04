"""Copy only small committed predecessor exports; never change a shared cache."""
from pathlib import Path
import shutil,hashlib,json,lzma
B=Path('/home/dombarker/project-offloads/codex-cx-carriers-bind-20261105')
C=Path('/home/dombarker/project-offloads/codex-cx-carriers-bind-cache-20261104')
P=Path('/home/dombarker/project-offloads/codex-cx-history-persist-cache-20261104')
B.mkdir(exist_ok=True);C.mkdir(exist_ok=True);rows=[]
for d in ['NGR_exports_20261105','NGP_exports_20261105','NGK_exports_20261105','NGC_exports_20261104']:
 for src in sorted((P/d).rglob('*')):
  if not src.is_file():continue
  dst=C/src.relative_to(P);dst.parent.mkdir(parents=True,exist_ok=True)
  if not dst.exists():shutil.copy2(src,dst)
  sha=hashlib.sha256(src.read_bytes()).hexdigest();assert hashlib.sha256(dst.read_bytes()).hexdigest()==sha
  rows.append(dict(source=str(src),path=str(dst),sha256=sha,bytes=dst.stat().st_size))
raw=json.dumps(rows).encode();(B/'NGS_CACHE_IMPORTS.json.xz').write_bytes(lzma.compress(raw));(B/'NGS_CACHE_IMPORTS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
shutil.copy2('/home/dombarker/project-offloads/codex-cx-pool-retarget-20261105/S2W_run_host.py',B/'S2W_run_host.py')
print(json.dumps(dict(files=len(rows),bytes=sum(r['bytes'] for r in rows),manifest_sha256=hashlib.sha256(raw).hexdigest())))
