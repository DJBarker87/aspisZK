"""End-of-lane cleanup of exact disposable compiler target paths, never caches."""
from NEO_remote import *
assert not (E/'NEO_ACTIVE.json').exists()
code=f'''from pathlib import Path
import json,shutil,datetime
b=Path({B!r});candidates=[b/'NEO_target']+list(b.glob('NEO_*_ref/target'));out=[]
for p in candidates:
 if not p.exists():continue
 assert not p.is_symlink() and p.resolve().parent.resolve() in [b.resolve()]+[q.resolve() for q in b.glob('NEO_*_ref')]
 keys=[str(q) for q in p.rglob('*.json') if any(s in q.name.lower() for s in ['keypair','wallet','account-key'])]
 if keys:out.append(dict(path=str(p),action='retained',key_candidates=keys));continue
 size=sum(q.stat().st_size for q in p.rglob('*') if q.is_file() and not q.is_symlink())
 shutil.rmtree(p);out.append(dict(path=str(p),action='removed compiler target only',bytes=size,key_candidates=[]))
print(json.dumps(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),paths=out,own_cache_deleted=False,shared_cache_touched=False,compiled_lean_objects='retained in pinned owned workspace/cache for dependent reuse',keys_touched=False)))
'''
r=ssh('NEO_FINISH_SCRATCH','python3',code);assert r.returncode==0,r.stderr
(E/'NEO_SCRATCH_FINAL.json').write_text(r.stdout);print(r.stdout)
