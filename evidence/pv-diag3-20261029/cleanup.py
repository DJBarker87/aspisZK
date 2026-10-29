"""Remove only this job's validated compiled scratch; never follow symlinks.
Sources, evidence, shared caches and keys are retained untouched."""
from pathlib import Path
import json,hashlib,shutil
D=Path('/home/dombarker/project-offloads/codex-pv-diag3-20261029')
assert json.loads((D/'final-post.json').read_text())['mismatches']==[]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
artifacts=[];links=0
O=D/'objects'
for p in O.rglob('*'):
 if p.is_dir() and not p.is_symlink():continue
 assert p.name.endswith(('.olean','.olean.server','.olean.private','.ir')),p
 if p.is_symlink():links+=1;continue
 artifacts.append(dict(path=str(p),sha256=sha(p),bytes=p.stat().st_size))
p=D/'native-controls';expected=json.loads((D/'native-controls.json').read_text())['binary_sha256']
assert sha(p)==expected
exe=dict(path=str(p),sha256=expected,bytes=p.stat().st_size)
shutil.rmtree(O);p.unlink()
(D/'cleanup.json').write_text(json.dumps(dict(artifact_pins=artifacts,removed_executable=exe,removed_private_links=links,shared_targets_removed=False,key_operations=0,sources_and_receipts_retained=True),indent=2)+'\n')
print('removed private compiled scratch',len(artifacts),'files, links',links,'probe executable1; no shared targets or keys')
