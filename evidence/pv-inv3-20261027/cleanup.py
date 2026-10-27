from pathlib import Path
import json,hashlib,shutil
b=Path('/home/dombarker/project-offloads/codex-pv-inv-20261027');o=b/'inv3/objects';rows=[]
for p in (o/'R1Z').glob('PV_Inv_*.olean'):
 if p.is_file() and not p.is_symlink():rows.append(dict(path=str(p),bytes=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest()))
(b/'inv3/own-object-hashes.json').write_text(json.dumps(rows,indent=2)+'\n')
print('own objects',len(rows))
# Only this continuation's compiled scratch. Directory symlinks are not followed.
shutil.rmtree(o)
k=b/'inv3-kani';removed=[]
for p in k.glob('PV_Inv_control*'):
 if p.name=='PV_Inv_control.rs':continue
 removed.append(dict(name=p.name,kind='directory' if p.is_dir() else 'file'))
 if p.is_dir():shutil.rmtree(p)
 else:p.unlink()
(b/'inv3/cleanup.json').write_text(json.dumps(dict(private_objects_removed=True,kani_scratch_removed=removed,shared_sources_modified=False,shared_objects_modified=False,wallet_keys_created_or_removed=False),indent=2)+'\n')
print('kani scratch',len(removed))
