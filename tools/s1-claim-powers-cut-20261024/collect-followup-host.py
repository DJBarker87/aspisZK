#!/usr/bin/env python3
"""Collect normal-return source experiments, retaining failures without proof credit."""
from pathlib import Path
import hashlib,json,shutil,tarfile,sys
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');O=H/'s1-native-control-followup-export-20261024';O.mkdir(exist_ok=False)
def copy(p,q):q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q)
for name in ['s1-claim-loop-contract-v4','s1-claim-loop-contract-v4-mir1','s1-original-ordered-tape-v2','s1-claim-ordered-tape-v1-sat-v2']:
 r=H/'receipts'/name;assert (r/'receipt.json').is_file(),('not terminal',name)
 for p in r.iterdir():
  if p.is_file() and p.suffix in ['.json','.log']:copy(p,O/'attempts'/name/p.name)
 for suffix in ['input','admission','global-admission','all-local-before','all-local-after','dependency-postcheck']:
  p=H/(name+'-'+suffix+'.json')
  if p.is_file():copy(p,O/'attempts'/name/(suffix+'.json'))
for name in ['s1-claim-loop-contract-v4-20261024','s1-original-ordered-tape-v2-20261024']:
 root=H/name
 for p in root.rglob('*'):
  if p.is_file() and not any(x in ['target','.git'] for x in p.relative_to(root).parts) and p.suffix in ['.rs','.toml','.lock','.json','.log','.c','.h']:
   copy(p,O/'inputs'/name/p.relative_to(root))
for name in ['prepare-loop-v4-host.py','run-loop-mir1-host.py','prepare-original-tape-host.py','run-tape-sat-host.py']:
 copy(H/name,O/'runners'/name)
for suffix in ['admission','global-admission']:
 copy(H/('s1-claim-ordered-tape-v1-sat-'+suffix+'.json'),O/'admission-rejected'/ (suffix+'.json'))
files={str(p.relative_to(O)):hashlib.sha256(p.read_bytes()).hexdigest() for p in O.rglob('*') if p.is_file()}
(O/'manifest.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',files=files,qualification='Source-only diagnostics and normal-return leaf-contract experiments. Tiny range capability is not verifier correctness. Failed/timeout attempts carry no semantic credit; no native arithmetic, SDK state or whole S1 closure.'),indent=2)+'\n')
with tarfile.open(str(O)+'.tar.gz','w:gz') as t:
 for p in O.rglob('*'):
  if p.is_file():t.add(p,arcname=p.relative_to(O))
print(json.dumps(dict(files=len(files),archive=str(O)+'.tar.gz')))
