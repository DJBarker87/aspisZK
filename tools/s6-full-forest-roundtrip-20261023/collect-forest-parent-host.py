#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,shutil,tarfile
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');O=H/'s6-forest-parent-export-v1';O.mkdir(exist_ok=False)
def copy(p,q):q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q)
K=H/'aspis-s6-native-snapshot-helper-v1';P=H/'s6-forest-parent-extract-v1'
for p in K.rglob('*'):
 if p.is_file() and not any(x in ['target','.git'] for x in p.relative_to(K).parts) and p.suffix in ['.rs','.toml','.lock','.json']:copy(p,O/'native-input'/p.relative_to(K))
for p in P.rglob('*'):
 if p.is_file() and p.suffix in ['.lean','.json','.llbc','.rs','.toml','.lock']:copy(p,O/'extraction'/p.relative_to(P))
for tag in ['s6-forest-parent-charon-v1','s6-forest-parent-aeneas-v1']:
 for p in (H/'receipts'/tag).iterdir():
  if p.is_file():copy(p,O/'attempts'/tag/p.name)
 for suffix in ['input','admission','global-admission','all-local-before','all-local-after','dependency-postcheck']:
  p=H/(tag+'-'+suffix+'.json')
  if p.is_file():copy(p,O/'attempts'/tag/(suffix+'.json'))

for n in ['prepare-snapshot-helper-host.py','run-owned-frontier-v2-host.py','extract-forest-parent-host.py']:copy(H/n,O/'runners'/n)
files={str(p.relative_to(O)):hashlib.sha256(p.read_bytes()).hexdigest() for p in O.rglob('*') if p.is_file()}
(O/'manifest.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',files=files,qualification='Unchanged frozen full forest validator and encoder extraction. Four explicit source children are concretely installed from separately checked payment, lane-transition and digest implementations. Prior reference transformations still require contextual transport, runtime/SDK joins and artifact re-pins. No whole S6 closure.'),indent=2)+'\n')
with tarfile.open(str(O)+'.tar.gz','w:gz') as t:
 for p in O.rglob('*'):
  if p.is_file():t.add(p,arcname=str(p.relative_to(O)))
