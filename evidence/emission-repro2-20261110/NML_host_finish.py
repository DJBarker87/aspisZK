"""Read-only final source/process audit; remove only owned rebuildable outputs."""
from pathlib import Path
import os,json,hashlib,shutil,time
B=Path('/home/dombarker/project-offloads/codex-cx-emission-repro2-20261110');assert B.resolve()==B
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
active=[]
for p in Path('/proc').iterdir():
 if not p.name.isdigit() or int(p.name)==os.getpid():continue
 try:
  cwd=(p/'cwd').resolve(strict=True)
  if cwd==B or B in cwd.parents:active.append(dict(pid=int(p.name),cwd=str(cwd),command=(p/'cmdline').read_bytes().replace(b'\0',b' ').decode(errors='replace')))
 except (OSError,RuntimeError):pass
assert not active,active
manifest=json.loads((B/'NML_STAGING_MANIFEST.json').read_text());w=B/'NML_workspace';drift=[n for n,v in manifest['files'].items() if not (w/n).is_file() or sha(w/n)!=v['sha256']];assert not drift,drift
size=lambda p:sum(f.stat().st_size for f in p.rglob('*') if f.is_file()) if p.exists() else 0
before=size(B);removed=[];artifacts={}
for name in ['NHR_target','NML_objects']:
 p=B/name
 if not p.exists():continue
 assert not p.is_symlink() and p.resolve().parent==B
 if name=='NML_objects':artifacts={str(f.relative_to(B)):dict(sha256=sha(f),bytes=f.stat().st_size) for f in p.rglob('*') if f.is_file()}
 n=size(p);shutil.rmtree(p);removed.append(dict(path=str(p),bytes=n,reason='Owned rebuildable Cargo output / new proof object scratch; not the retained prepared cache'))
post=dict(time_unix=time.time(),active_owned_processes=active,frozen_source_drift=drift,lock_sha256=sha(w/'Cargo.lock'),expected_lock_sha256=manifest['files']['Cargo.lock']['sha256'],owned_bytes_before=before,removed_rebuildable_outputs=removed,owned_bytes_after=size(B),free_bytes=shutil.disk_usage(B).free,compiled_artifact_hashes=artifacts,retained_cache_untouched='/home/dombarker/project-offloads/codex-cx-slice-d-prepared-cache-20261104',launcher_sha256=sha(B/'S2W_run_host.py'),tool_sha256={n:sha(Path('/home/dombarker/project-offloads/codex-cx-extraction-repro1-20261027/XRa_bin')/n) for n in ['charon','aeneas-b59d5188-extended']})
assert post['owned_bytes_after']<30_000_000_000 and post['free_bytes']>=40_000_000_000
(B/'NML_HOST_POSTCHECK.json').write_text(json.dumps(post,indent=2)+'\n');print(json.dumps(post))
