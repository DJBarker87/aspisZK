from pathlib import Path
import shutil,json,hashlib,re
B=Path(__file__).resolve().parent
(B/'NKJ_native').mkdir(exist_ok=True)
pins={}
for n in ['NFA_WALKER.c','NFA_MemoryLimit.c']:
 p=Path('/home/dombarker/project-offloads/codex-cx-slice-d-define-20261104/NFQ_native')/n;q=B/'NKJ_native'/n
 shutil.copy2(p,q);pins[n]=dict(origin=str(p),sha256=hashlib.sha256(q.read_bytes()).hexdigest(),bytes=q.stat().st_size)
# Preserve the byte-identical NEP walker input separately from driver adaptations.
(B/'NKJ_AUDIT_SUPPORT_PINS.json').write_text(json.dumps(pins,indent=2))
print('NKJ immutable native audit support copied')
