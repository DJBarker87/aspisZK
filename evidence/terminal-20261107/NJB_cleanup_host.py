from pathlib import Path
import json,hashlib,shutil,subprocess
B=Path('/home/dombarker/project-offloads/codex-cx-terminal-20261107').resolve();C=Path('/home/dombarker/project-offloads/codex-cx-slice-d-prepared-cache-20261104/NJB_20261107').resolve();export=json.loads((B/'NJB_EXPORT.json').read_text());assert Path(export['cache']).resolve().is_relative_to(C)
for row in export['files']:
 q=Path(row['path']);assert q.resolve().is_relative_to(C);assert hashlib.sha256(q.read_bytes()).hexdigest()==row['sha256']
removed=[]
for name in ['NJB_target','NJB_objects','NJB_native','NJB_tmp']:
 p=B/name;assert p.parent==B and not p.resolve().is_relative_to(C)
 if not p.exists():continue
 size=sum(q.stat().st_size for q in p.rglob('*')if q.is_file()and not q.is_symlink());shutil.rmtree(p);removed.append(dict(path=str(p),bytes=size))
# No deletion in /tmp without positive job attribution; the explicit own TMPDIR
# is covered above. Shared caches, workspaces, keys and every retained export stay intact.
r=dict(retained_cache=str(C),retained_export_verified=True,deleted=removed,shared_or_foreign_paths_deleted=[],keys_touched=False,remaining_directories=sorted(p.name for p in B.iterdir()if p.is_dir()),disk=subprocess.check_output(['df','-B1',str(B)],text=True))
(B/'NJB_CLEANUP.json').write_text(json.dumps(r,indent=1));print(json.dumps(r))
