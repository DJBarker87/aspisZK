"""Hash then delete only this task's large register/instruction trace files.
Signing keys and all task sidecars are retained. Run after analysis validation.
"""
import hashlib,json,sys
from pathlib import Path
H=Path(sys.argv[1]).resolve();T=H/'traces';rows=[]
assert H.name=='codex-cx-cu-bound5-20261020'
for p in sorted(T.rglob('*')):
 if not p.is_file() or p.suffix not in ('.regs','.insns'):continue
 assert p.resolve().is_relative_to(T)
 h=hashlib.sha256()
 with p.open('rb') as f:
  while block:=f.read(8*1024*1024):h.update(block)
 rows.append(dict(path=str(p.relative_to(H)),bytes=p.stat().st_size,sha256=h.hexdigest(),deleted=False))
(H/'trace-inventory.json').write_text(json.dumps(rows,indent=1))
for row in rows:
 p=H/row['path'];assert p.stat().st_size==row['bytes'];p.unlink();row['deleted']=True
(H/'trace-inventory.json').write_text(json.dumps(rows,indent=1))
print(json.dumps(dict(deleted_files=len(rows),deleted_bytes=sum(r['bytes'] for r in rows),wallet_keys_deleted=0,task_keys='retained',inventory=str(H/'trace-inventory.json'))))
