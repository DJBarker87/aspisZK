#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,shutil,tarfile
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');O=H/'s6-owned-frontier-export-v1';O.mkdir(exist_ok=False)
def copy(p,q):q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q)
K=H/'aspis-s6-native-owned-frontier-v1';P=H/'s6-owned-frontier-extract-v1'
for p in K.rglob('*'):
 if p.is_file() and not any(x in ['target','.git'] for x in p.relative_to(K).parts) and p.suffix in ['.rs','.toml','.lock','.json']:copy(p,O/'native-input'/p.relative_to(K))
for p in P.rglob('*'):
 if p.is_file() and p.suffix in ['.lean','.json','.llbc']:copy(p,O/'extraction'/p.relative_to(P))
for tag in ['s6-native-owned-frontier-v2','s6-owned-frontier-charon-v1','s6-owned-frontier-aeneas-v1']:
 for p in (H/'receipts'/tag).iterdir():
  if p.is_file():copy(p,O/'attempts'/tag/p.name)
 for suffix in ['input','admission','global-admission','all-local-before','all-local-after','dependency-postcheck']:
  p=H/(tag+'-'+suffix+'.json')
  if p.is_file():copy(p,O/'attempts'/tag/(suffix+'.json'))
copy(H/'s6-native-owned-frontier-v1-global-admission.json',O/'excluded-admission/native-v1.json')
for n in ['prepare-owned-frontier-host.py','run-owned-frontier-host.py','run-owned-frontier-v2-host.py','extract-owned-frontier-host.py']:copy(H/n,O/'runners'/n)
files={str(p.relative_to(O)):hashlib.sha256(p.read_bytes()).hexdigest() for p in O.rglob('*') if p.is_file()}
(O/'manifest.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',files=files,qualification='Full native carrier frontier reference: original frozen foreach versus owned-buffer helper loop checked at every byte. Digest leaf uses its exact separately checked concrete equivalent. Focused helper/loop extraction has one explicit digest leaf, to be installed from the checked source model; no fake/simplified afterstate or account carrier. No enclosing codec/SDK or release closure.'),indent=2)+'\n')
with tarfile.open(str(O)+'.tar.gz','w:gz') as t:
 for p in O.rglob('*'):
  if p.is_file():t.add(p,arcname=str(p.relative_to(O)))
