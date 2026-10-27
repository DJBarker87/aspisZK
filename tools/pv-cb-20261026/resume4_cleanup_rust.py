"""Remove only this job's three disposable Rust build caches after all gates.
Preserve Lean objects, source, pinned tools, receipts and all other workspaces.
"""
from pathlib import Path
import subprocess,json
root=Path(__file__).resolve().parents[2];ev=root/'evidence/pv-cb-20261026'
receipts=[json.loads(p.read_text()) for p in ev.glob('kani-resume4-*/collected-receipt.json') if json.loads(p.read_text()).get('attempt_charged')]
assert len(receipts)==12,'Do not clean build caches before all12 gates are receipted'
code='''from pathlib import Path
import json,shutil
base=Path('/home/dombarker/project-offloads/codex-pv-cb-20261026')
r=[]
for name in ['source-kani-target','config-target','charon-target']:
 p=base/name;assert p.parent==base and p.is_dir() and not p.is_symlink()
 # These exact directories were cargo target dirs, never wallet or source dirs.
 assert (p/'CACHEDIR.TAG').exists() or (p/'debug').is_dir() or (p/'release').is_dir() or (p/'kani').is_dir()
 size=sum(q.stat().st_size for q in p.rglob('*') if q.is_file())
 shutil.rmtree(p);r.append(dict(path=str(p),bytes_removed=size,exists_after=p.exists()))
print(json.dumps(dict(removed=r,preserved=['lean-objects','pinned-tools','source','proof sources and receipts'],keys_created_or_deleted=0),indent=2))
'''
s=subprocess.check_output(['ssh','dombarker@100.108.41.90','python3','-'],input=code,text=True)
(ev/'RESUME4-RUST-CACHE-CLEANUP.json').write_text(s+'\n');print(s)
