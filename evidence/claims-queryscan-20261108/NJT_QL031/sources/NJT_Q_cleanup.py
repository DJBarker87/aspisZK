from pathlib import Path
import hashlib,json,shutil,os
B=Path(__file__).resolve().parent;sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for name in ['NJT_QEXPORT.json','NJT_QCLAIMS_EXPORT.json']:
 x=json.loads((B/name).read_text())
 for p in x['files']:assert sha(Path(p['path']))==p['sha256'],p['path']
for name in ['NJT_Q_SOURCE_PINS.json','NJT_Q_FROZEN_FILE_PINS.json']:
 for n,h in json.loads((B/name).read_text()).items():assert sha(B/'NJT_Q_src'/n)==h,n
assert sha(B/'NJT_Q_src/Cargo.lock')=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
free=lambda:os.statvfs(B).f_bavail*os.statvfs(B).f_frsize
before=free();deleted=[]
for name in ['NJT_Q_target','NJT_Q_tmp']:
 p=B/name
 if p.exists():
  size=sum(q.stat().st_size for q in p.rglob('*') if q.is_file());shutil.rmtree(p);deleted.append(dict(path=str(p),bytes=size))
(B/'NJT_QFINAL_HOST.json').write_text(json.dumps(dict(removed_rebuildable_outputs=deleted,free_bytes_before=before,free_bytes_after=free(),retained_exports=['NJT_Q_exports_20261108','NJT_QClaims_exports_20261108'],source_manifests_unchanged=True,frozen_lock_unchanged=True,cargo_target_dir=str(B/'NJT_Q_target'),cache_deleted=False,keys_touched=False),indent=2));print('own target/temp removed; exports/source/lock retained and verified')
