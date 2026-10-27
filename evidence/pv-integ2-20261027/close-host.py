"""Remove only task-owned rebuildable caches; preserve every key and receipt."""
from pathlib import Path
import json,hashlib,shutil
D=Path('/home/dombarker/project-offloads/codex-pv-integ2-20261027');assert D.name=='codex-pv-integ2-20261027'
keys=json.loads((D/'key-retention.json').read_text())
for r in keys['keys']:
 p=Path(r['path']);assert p.is_file() and (p.stat().st_mode&0o777)==0o600
 assert bytes(json.loads(p.read_text())[32:]).hex()==r['public_key_hex']
removed=[];retained=[];objects=[]
for p in (D/'objects').rglob('*.olean'):
 if p.stat().st_nlink==1:objects.append(dict(path=str(p.relative_to(D)),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size))
for name in ['sbf-target-verifier','sbf-target-pool','objects']:
 p=D/name
 if not p.exists():continue
 assert not p.is_symlink()
 protected=[]
 for f in p.rglob('*.json'):
  try:v=json.loads(f.read_text())
  except (ValueError,UnicodeError):continue
  if f.name.endswith('-keypair.json') or (isinstance(v,list) and len(v)==64 and all(isinstance(x,int) and 0<=x<=255 for x in v)):protected.append(str(f))
 if protected:retained.append(dict(path=str(p),reason='possible key material; no deletion',files=protected));continue
 shutil.rmtree(p);removed.append(str(p))
(D/'cleanup.json').write_text(json.dumps(dict(removed_rebuildable_caches=removed,retained_caches=retained,new_object_hashes=objects,retained_keys=keys,no_key_cleanup=True,no_transactions=True,shared_cache_unmodified=True),indent=2)+'\n')
print('removed caches',len(removed),'retained caches',len(retained),'keys retained',len(keys['keys']))
