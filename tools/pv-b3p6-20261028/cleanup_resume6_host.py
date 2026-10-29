"""End-of-round proof-object hygiene; never removes source or key material."""
from pathlib import Path
import hashlib,json,shutil,time
from run import H
p=H/'lean-objects';rows=[]
assert p.is_dir()
for q in sorted(p.rglob('*')):
 if not q.is_file():continue
 assert q.suffix in {'.olean','.ilean'},('unexpected file: retained; cleanup refused',str(q))
 rows.append(dict(path=str(q.relative_to(H)),sha256=hashlib.sha256(q.read_bytes()).hexdigest(),bytes=q.stat().st_size))
(H/'resume6-object-manifest.json').write_text(json.dumps(rows,indent=2)+'\n')
size=sum(r['bytes']for r in rows)
shutil.rmtree(p)
(H/'cleanup-resume6.json').write_text(json.dumps(dict(reason='local-lean rule9; round complete after all100 attempts and dependent audits; sources and all receipts retained',path=str(p),objects=len(rows),bytes_removed=size,rebuildable=True,keys_deleted=False,shared_directories_written=False,epoch=time.time()),indent=2)+'\n')
print(json.dumps(dict(objects=len(rows),bytes_removed=size)))
