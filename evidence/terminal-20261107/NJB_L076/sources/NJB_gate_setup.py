from pathlib import Path
import hashlib,json,shutil
b=Path.cwd();p=Path('/home/dombarker/project-offloads/codex-cx-ledger13-20261107/NIU_native');rows=[]
for n in ['NFA_WALKER.c','NFA_MemoryLimit.c']:
 q=p/n;r=b/'NJB_native'/n;shutil.copyfile(q,r);rows.append(dict(source=str(q),target=str(r),sha256=hashlib.sha256(r.read_bytes()).hexdigest(),bytes=r.stat().st_size))
(b/'NJB_GATE_PINS.json').write_text(json.dumps(rows,indent=1));print('unchanged walker/memory C source copied and pinned')
