from pathlib import Path
import json,shutil
D=Path('/home/dombarker/project-offloads/codex-pv-rdcd-20261028');removed=[]
for name in ['target','classification-target','lean-objects','external-objects']:
 p=D/name
 if p.exists():
  assert p.parent==D and not p.is_symlink();shutil.rmtree(p);removed.append(str(p))
for name in ['zeroize-native','zeroize-drop']:
 p=D/'zeroize-fixture'/name
 if p.exists():assert p.is_file() and not p.is_symlink();p.unlink();removed.append(str(p))
(D/'cleanup.json').write_text(json.dumps(dict(removed=removed,scope='Only this job compiled caches, read-only external symlinks and two fixture binaries. Sources, manifests, logs and receipts retained. No wallet/account keys created, inventoried for cleanup or removed; no other job path written.'),indent=2)+'\n');print('Removed',len(removed),'own rebuildable cache/binary paths')
