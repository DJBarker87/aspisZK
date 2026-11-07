"""Post-processing hygiene: remove only this job's rebuildable outputs after export verification."""
from PCD_transport import *
import hashlib
r=ssh('python3',f'''from pathlib import Path
import json,hashlib,shutil,os
b=Path({B!r});info=json.loads((b/'PCD_EXPORT.json').read_text())
for item in info['copies']:
 p=Path(item['export']);assert p.is_file()
 assert hashlib.sha256(p.read_bytes()).hexdigest()==item['sha256']
removed=[]
# These are compiler/solver/linker scratch only, not source, retained exports or keys.
for name in ['PCD_target','PCD_actual_extract_target','PCD_objects','PCD_native','PCD_tmp']:
 p=b/name
 assert p.parent==b and not p.is_symlink()
 if p.is_dir():
  count=sum(1 for q in p.rglob('*') if q.is_file());shutil.rmtree(p);removed.append(dict(path=str(p),files=count))
summary=dict(status='OWN_REBUILDABLE_OUTPUTS_REMOVED',removed=removed,export_verified=True,export=info['export'],cache_root_retained=b.is_dir(),sources_retained=True,seed_exports_retained=True,sibling_paths_touched=[],keys_created_used_deleted=False,free_bytes=shutil.disk_usage(b).free,method='filesystem post-processing only; no new compile/prover/audit scope')
(b/'PCD_CLEANUP.json').write_text(json.dumps(summary,indent=1)+'\\n');print(json.dumps(summary))
''')
assert r.returncode==0,r.stderr
(E/'PCD_CLEANUP.json').write_text(r.stdout)
print('Verified retained exports and removed only own compiler/solver/linker scratch; cache root, sources, seeds and all sibling paths retained.')
