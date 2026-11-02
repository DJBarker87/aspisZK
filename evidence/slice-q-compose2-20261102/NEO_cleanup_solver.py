"""Remove only this lane's terminal solver scratch, never any cache or key."""
from NEO_remote import *
import hashlib
assert not (E/'NEO_ACTIVE.json').exists()
a='NEO_SOLVER_CLEANUP'
code=f'''from pathlib import Path
import json,os,datetime
root=Path({B!r})/'NEO_tmp';items=[]
for p in root.rglob('*'):
 if p.is_file() and (p.name.startswith('external-sat') and p.suffix=='.cnf' or p.name.startswith('smt2_dec_problem')):
  assert root.resolve() in p.resolve().parents and p.stat().st_uid==os.getuid()
  items.append(dict(path=str(p),bytes=p.stat().st_size));p.unlink()
print(json.dumps(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),owned_root=str(root),deleted=items,total_bytes=sum(i['bytes'] for i in items),no_active_own_prover=True,cache_deleted=False,keys_touched=False)))
'''
r=ssh(a,'python3',code);assert r.returncode==0,r.stderr
(E/'NEO_SOLVER_CLEANUP.json').write_text(r.stdout);print(r.stdout)
