"""Remove only this job's rebuildable outputs after final evidence collection."""
from pathlib import Path
import shutil,json
D=Path('/home/dombarker/project-offloads/codex-pv-rdcd-20261028');removed=[]
for name in ['target','classification-target','resume-extract-target','lean-objects','external-objects']:
 p=D/name
 if p.exists():
  assert p.parent==D and not p.is_symlink();shutil.rmtree(p);removed.append(str(p))
(D/'resume-cleanup.json').write_text(json.dumps(dict(removed=removed,scope='Own compiled Rust/Lean targets and external-object symlinks only; all source, LLBC, generated text, pins, logs and receipts retained. No wallet/account keys created or removed; no other job directory modified.'),indent=2)+'\n');print('Removed',len(removed),'own rebuildable cache paths; evidence retained')
