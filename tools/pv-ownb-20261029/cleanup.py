"""Remove only this task's rebuildable object/target caches after final replay."""
from pathlib import Path
import json,hashlib,shutil
D=Path('/home/dombarker/project-offloads/codex-pv-ownb-20261029');O=D/'lean-objects';target=D/'target'
exe=target/'release/layout_probe'
record=dict(executable=dict(sha256=hashlib.sha256(exe.read_bytes()).hexdigest(),size=exe.stat().st_size),links=0,objects=0,object_bytes=0,cargo_target_bytes=0,scope='own rebuildable compiler output only; sources, MIR, receipts and source snapshots retained; no keys created or removed')
files=list(O.rglob('*'))
for p in files:
 if p.is_symlink():record['links']+=1;p.unlink()
 elif p.is_file():
  assert p.suffix=='.olean',str(p)
  record['objects']+=1;record['object_bytes']+=p.stat().st_size;p.unlink()
for p in sorted(O.rglob('*'),key=lambda p:len(p.parts),reverse=True):
 if p.is_dir():p.rmdir()
O.rmdir()
for p in target.rglob('*'):
 if p.is_file() and not p.is_symlink():record['cargo_target_bytes']+=p.stat().st_size
shutil.rmtree(target)
(D/'cleanup.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(record))
