from pathlib import Path
import json,shutil,stat
D=Path('/home/dombarker/project-offloads/codex-pv-dict2-20261027');rows=[]
for name in ['lean-objects','sbf-target-verifier','sbf-target-pool']:
 p=D/name
 if not p.exists():continue
 assert p.parent==D and p.is_dir() and not p.is_symlink()
 keys=[]
 for f in p.rglob('*.json'):
  if f.is_symlink() or not f.is_file() or f.stat().st_size>8192:continue
  try:data=json.loads(f.read_text())
  except (ValueError,UnicodeError):continue
  if isinstance(data,list) and len(data)==64 and all(type(x)==int and 0<=x<256 for x in data):keys.append(str(f))
 row=dict(path=str(p),retained_key_paths=keys,removed=False)
 if not keys:
  # shutil.rmtree removes symlinks as links and never traverses their targets.
  shutil.rmtree(p);row['removed']=True
 rows.append(row)
(D/'cleanup.json').write_text(json.dumps(dict(caches=rows,artifacts_and_keys_retained=True,no_shared_paths_modified=True),indent=2)+'\n');print(json.dumps(rows))
