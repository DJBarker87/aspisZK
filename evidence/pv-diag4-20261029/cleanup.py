from pathlib import Path
import json,hashlib,shutil
D=Path('/home/dombarker/project-offloads/codex-pv-diag4-20261029');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert json.loads((D/'final-post.json').read_text())['mismatches']==[]
for i in [64597,64598,64599]:assert json.loads((D/f'lean{i}-receipt.json').read_text())['exit']==0
artifacts=[];links=[];O=D/'objects'
for p in O.rglob('*'):
 if p.is_dir() and not p.is_symlink():continue
 assert p.name.endswith(('.olean','.olean.server','.olean.private','.ir')),p
 if p.is_symlink():links.append(dict(path=str(p),target=str(p.resolve())));continue
 artifacts.append(dict(path=str(p),sha256=sha(p),bytes=p.stat().st_size))
b=D/'native-controls';expected=json.loads((D/'leaf-bindings.json').read_text())['native_binary_sha256'];assert sha(b)==expected
binary=dict(path=str(b),sha256=expected,bytes=b.stat().st_size)
shutil.rmtree(O);b.unlink()
(D/'cleanup.json').write_text(json.dumps(dict(artifacts=artifacts,removed_private_links=len(links),removed_binary=binary,shared_targets_removed=False,source_or_receipt_removed=False,key_operations=0),indent=2)+'\n');print('removed own compiled scratch',len(artifacts),'files and',len(links),'private links; no shared targets, sources, receipts or keys')
