"""Remove only this job's compiled object scratch; never follow imported links."""
from pathlib import Path
import json,subprocess,shlex
E=Path('evidence/pv-rj4id-20261029')
code=r'''import pathlib,json
p=pathlib.Path('/home/dombarker/project-offloads/codex-pv-rj4id-20261029/objects');removed=[]
assert p.is_dir() and not p.is_symlink()
for q in p.rglob('*'):
 if q.is_symlink() or q.is_file():
  assert q.name.endswith(('.olean','.olean.server','.olean.private','.ir')),(q,'unexpected file; keep all scratch')
for q in p.rglob('*'):
 if q.is_symlink() or q.is_file():
  removed.append(dict(path=str(q),symlink=q.is_symlink(),target=str(q.readlink()) if q.is_symlink() else None));q.unlink()
print(json.dumps(dict(only_own_object_files_unlinked=True,removed=removed,shared_targets_unmodified=True,sources_and_receipts_retained=True,wallet_or_account_keys_touched=False)))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],text=True,capture_output=True);assert r.returncode==0,r.stderr
(E/'cleanup.json').write_text(r.stdout);print('removed only own object scratch:',len(json.loads(r.stdout)['removed']))
