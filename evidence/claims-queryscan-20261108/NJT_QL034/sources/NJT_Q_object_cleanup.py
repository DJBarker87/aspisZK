from pathlib import Path
import hashlib,json,shutil,os
B=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
verified=[]
for name in ['NJT_QEXPORT.json','NJT_QCLAIMS_EXPORT.json']:
 x=json.loads((B/name).read_text())
 for p in x['files']:
  q=Path(p['path']);assert q.is_file() and sha(q)==p['sha256'],p['path']
 verified.append(dict(manifest=name,manifest_sha256=sha(B/name),export=x['export'],files=len(x['files']),bytes=x['total_bytes']))
free=lambda:os.statvfs(B).f_bavail*os.statvfs(B).f_frsize
before=free();removed=[]
for name in ['NJT_Q_objects','NJT_Q_native']:
 p=B/name;assert p.parent==B and not p.is_symlink()
 assert str(B)=='/home/dombarker/project-offloads/codex-cx-claims-queryscan-20261108-query'
 if p.exists():
  size=sum(q.stat().st_size for q in p.rglob('*') if q.is_file());files=sum(1 for q in p.rglob('*') if q.is_file())
  shutil.rmtree(p);removed.append(dict(path=str(p),bytes=size,files=files))
for x in verified:assert Path(x['export']).is_dir()
(B/'NJT_QOBJECT_CLEANUP.json').write_text(json.dumps(dict(verified_exports=verified,removed_rebuildable_scratch=removed,free_bytes_before=before,free_bytes_after=free(),sources_receipts_seeds_caches_retained=True,no_non_job_path_removed=True,keys_touched=False,proof_or_audit_rerun=False,cargo_target_dir=str(B/'NJT_Q_target')),indent=2))
print('retained exports hash-verified; only owned object/native scratch removed')
