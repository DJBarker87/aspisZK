"""Verify retained exports, then remove only this job's compiled scratch."""
from pathlib import Path
import hashlib,json,shutil,os
P=Path('/home/dombarker/project-offloads');B=P/'codex-cx-ledger7-20261104';C=P/'codex-cx-ledger7-cache-20261104'
active=[]
for proc in Path('/proc').iterdir():
 if not proc.name.isdigit():continue
 try:
  exe=os.readlink(proc/'exe');cwd=os.readlink(proc/'cwd');cmd=(proc/'cmdline').read_bytes().replace(b'\0',b' ').decode(errors='replace')
 except (FileNotFoundError,PermissionError,ProcessLookupError):continue
 if (exe.startswith(str(B)+'/NFX_native/') or (cwd==str(B) and 'S2W_run_host.py' in cmd)):active.append(dict(pid=proc.name,exe=exe,command=cmd))
assert not active,active
# The export manifest is supplied independently from the local committed source.
manifest=json.loads((B/'NFX_EXPORT_MANIFEST.json').read_text())
for r in manifest['objects']:
 p=Path(r['path']);assert p.is_relative_to(C) and p.stat().st_size==r['bytes'] and hashlib.sha256(p.read_bytes()).hexdigest()==r['sha256']
deleted=[]
for name in ['NFX_objects','NFX_native']:
 d=B/name
 for p in d.rglob('*'):
  if not p.is_file():continue
  assert p.name.startswith(('NFX_','NFA_')),p
  assert p.name.endswith(('.olean','.olean.private','.olean.server','.ir','.c')) or p.name in ['NFX_ProofDriver','NFX_Driver','NFX_InventoryDriver'],p
  deleted.append(dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size))
 shutil.rmtree(d)
print(json.dumps(dict(active_owned_builds=active,retained_cache=str(C),retained_exports_verified=len(manifest['objects']),removed_compiled_scratch=deleted,cache_deleted=False,source_or_key_deleted=False,free_bytes=shutil.disk_usage(P).free),indent=1))
