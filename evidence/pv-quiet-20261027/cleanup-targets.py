from pathlib import Path
import json,shutil,time
H=Path('/home/dombarker/project-offloads/codex-pv-quiet-20261027')
assert (H/'window-end.json').exists(),'measurement process has not exited'
assert not (H.parent/'QUIET_WINDOW.json').exists(),'quiet marker remains'
rows=[]
for side in ['control','candidate']:
 p=H/side/'target';assert p.resolve()==p
 before=p.exists();shutil.rmtree(p) if before else None
 rows.append(dict(path=str(p),existed_before=before,exists_after=p.exists()))
(H/'cleanup.json').write_text(json.dumps(dict(utc=time.time(),cargo_targets=rows,keys_deleted=False,binaries_retained=True,raw_fixture_outputs_retained=True),indent=2)+'\n')
