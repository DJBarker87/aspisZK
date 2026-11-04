"""Retain final coherent NFX objects in the owned cache; never delete a cache."""
from pathlib import Path
import shutil,hashlib,json,subprocess
P=Path('/home/dombarker/project-offloads');B=P/'codex-cx-ledger7-20261104';C=P/'codex-cx-ledger7-cache-20261104';D=C/'NFX_exports_20261104';N=C/'NFX_native_20261104';D.mkdir(exist_ok=True);N.mkdir(exist_ok=True)
rows=[]
for module in ['NFX_COMBINED_IMPORT','NFX_ProofDriver','NFX_Driver']:
 for p in [B/'NFX_objects'/(module+s) for s in ['.olean','.olean.private','.olean.server','.ir']]+[B/'NFX_generated'/(module+'.lean')]:
  if p.exists():
   q=D/p.name;shutil.copy2(p,q);rows.append(dict(path=str(q),source=str(p),sha256=hashlib.sha256(q.read_bytes()).hexdigest(),bytes=q.stat().st_size))
for name in ['NFX_ProofDriver','NFX_Driver','NFX_ProofDriver.c','NFX_Driver.c','NFA_WALKER.c','NFA_MemoryLimit.c']:
 p=B/'NFX_native'/name;q=N/name;shutil.copy2(p,q);rows.append(dict(path=str(q),source=str(p),sha256=hashlib.sha256(q.read_bytes()).hexdigest(),bytes=q.stat().st_size))
launchers=[]
for name in ['S2W_run_host.py','S2W_lean_host.py']:
 p=B/name;original=P/'codex-cx-sound-int2-20261025'/name;assert p.read_bytes()==original.read_bytes();launchers.append(dict(path=str(p),original=str(original),sha256=hashlib.sha256(p.read_bytes()).hexdigest()))
print(json.dumps(dict(cache_retained=str(C),objects=rows,unchanged_launchers=launchers,source_or_key_cleanup=False,scopes_terminal=True),indent=1))
