"""Pin actual retained tools without changing shared infrastructure."""
from pathlib import Path
import hashlib,json,shutil
B=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
files=['S2W_run_host.py','NKK_native/NFA_WALKER.c','NKK_native/NFA_MemoryLimit.c']
rows=[dict(path=str(B/n),sha256=sha(B/n),bytes=(B/n).stat().st_size) for n in files]
T=Path('/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin')
rows += [dict(path=str(T/n),sha256=sha(T/n),bytes=(T/n).stat().st_size) for n in ['lean','lake','leanc']]
report=dict(files=rows,free_bytes=shutil.disk_usage(B).free,infrastructure_modified=False,cargo_target=str(B/'NKK_target'))
(B/'NKK_TOOL_PINS.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(dict(pinned=len(rows),free_bytes=report['free_bytes'])))
