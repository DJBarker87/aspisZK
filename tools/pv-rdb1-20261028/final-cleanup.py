from pathlib import Path
import json,hashlib,shutil
D=Path('/home/dombarker/project-offloads/codex-pv-rdb1-20261028')
artifacts=[]
for rel in ['witness-config/check','v181-native-config/check','classification-target/release/fixture']:
 p=D/rel
 if p.exists():
  b=p.read_bytes();assert b[:4]==b'\x7fELF';artifacts.append(dict(path=str(p),sha256=hashlib.sha256(b).hexdigest(),size=len(b)));p.unlink()
target=D/'classification-target';assert not target.is_symlink()
if target.exists():shutil.rmtree(target)
j=dict(removed_elf_fixtures=artifacts,removed_cargo_target=str(target),retained='all source, logs, receipts and shared Lean objects',keys='none created, accessed or removed',scope='own job rebuildable caches only')
(D/'cleanup-final.json').write_text(json.dumps(j,indent=2)+'\n');print(json.dumps(j))
