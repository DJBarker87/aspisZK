from pathlib import Path
import shutil,hashlib,json
B=Path.cwd();X=B.parent/'codex-pc-helpers1-cache-20261110/PCB_exports_20261110/PCB_native'
pins={}
for old,new in [('PCB_WALKER.c','PCG_WALKER.c'),('PCB_MemoryLimit.c','PCG_MemoryLimit.c')]:
 p=X/old;q=B/'PCG_native'/new;shutil.copyfile(p,q);pins[new]=dict(source=str(p),sha256=hashlib.sha256(q.read_bytes()).hexdigest(),bytes=q.stat().st_size)
(B/'PCG_AUDIT_BINARY_PINS.json').write_text(json.dumps(pins,indent=1)+'\n')
print('Copied pinned canonical NEP walker C inputs')
