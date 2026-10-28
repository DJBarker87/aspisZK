from pathlib import Path
import json,shutil,time
D=Path(__file__).resolve().parent
names=['sbf-target-verifier','sbf-target-pool','native-target','combined/baseline/native-target']
rows=[]
for name in names:
 p=D/name
 if not p.exists():rows.append(dict(path=str(p),existed=False));continue
 assert not p.is_symlink()
 keys=[str(q) for q in p.rglob('*') if q.is_file() and ('keypair' in q.name.lower() or q.name.lower().endswith(('.pem','.key')))]
 if keys:
  rows.append(dict(path=str(p),existed=True,deleted=False,retained_possible_keys=keys));continue
 shutil.rmtree(p);rows.append(dict(path=str(p),existed=True,deleted=True))
(D/'cleanup.json').write_text(json.dumps(dict(utc=time.time(),targets=rows,keys_deleted=0,keys_moved=0,transactions=0,refunds='N/A: no key cleanup authorized or performed'),indent=2)+'\n')
print(json.dumps(rows))
