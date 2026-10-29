from pathlib import Path
import json,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-diag7-20261029');rows=[]
for p in sorted((D/'objects').rglob('*')):
 if p.is_file() or p.is_symlink():
  assert p.suffix in {'.olean','.server','.private','.ir'},p
  rows.append(dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size))
  p.unlink()
(D/'cleanup.json').write_text(json.dumps(dict(deleted_private_compiler_objects=rows,shared_objects_modified=False,source_or_receipts_deleted=False,wallet_key_nonce_operations=False),indent=2)+'\n')
print('removed private compiler objects',len(rows))
