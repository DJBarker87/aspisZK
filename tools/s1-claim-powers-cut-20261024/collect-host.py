#!/usr/bin/env python3
"""Collect normal-return source experiments, retaining failures without proof credit."""
from pathlib import Path
import hashlib,json,shutil,tarfile,sys
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');O=H/'s1-loop-contract-export-20261024';O.mkdir(exist_ok=False)
def copy(p,q):q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q)
for name in ['s1-original-whole-powers-cut-v1','s1-claim-loop-contract-v1','s1-claim-loop-contract-v2','s1-claim-loop-contract-v2-backtrace','s1-claim-loop-contract-v3','s1-claim-ordered-tape-v1']:
 r=H/'receipts'/name;assert (r/'receipt.json').is_file(),('not terminal',name)
 for p in r.iterdir():
  if p.is_file() and p.suffix in ['.json','.log']:copy(p,O/'attempts'/name/p.name)
 for suffix in ['input','admission','global-admission','all-local-before','all-local-after','dependency-postcheck']:
  p=H/(name+'-'+suffix+'.json')
  if p.is_file():copy(p,O/'attempts'/name/(suffix+'.json'))
for name in ['s1-loop-contract-preflight-20261024','s1-loop-contract-preflight-v2-20261024','aspis-s1-claim-powers-cut-v1-20261024','s1-claim-loop-contract-v1-20261024','s1-claim-loop-contract-v2-20261024','s1-claim-loop-contract-v3-20261024','s1-claim-ordered-tape-v1-20261024','s1-loop-contract-preflight-v3-20261024','s1-loop-contract-preflight-v4-20261024']:
 root=H/name
 for p in root.rglob('*'):
  if p.is_file() and not any(x in ['target','.git'] for x in p.relative_to(root).parts) and p.suffix in ['.rs','.toml','.lock','.json','.log','.c','.h']:
   copy(p,O/'inputs'/name/p.relative_to(root))
for name in ['s1-run-powers-cut-20261024.py','s1-loop-preflight-runner-20261024.py','s1-loop-preflight-v2-runner-20261024.py','prepare-loop-host.py','prepare-loop-v2-host.py','run-loop-host.py','run-loop-diagnostic-host.py','prepare-loop-v3-host.py','prepare-tape-host.py','run-tape-host.py','s1-loop-preflight-v3-runner-20261024.py','s1-loop-preflight-v4-runner-20261024.py']:
 copy(H/name,O/'runners'/name)
files={str(p.relative_to(O)):hashlib.sha256(p.read_bytes()).hexdigest() for p in O.rglob('*') if p.is_file()}
(O/'manifest.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',files=files,qualification='Source-only diagnostics and normal-return leaf-contract experiments. Tiny range capability is not verifier correctness. Failed/timeout attempts carry no semantic credit; no native arithmetic, SDK state or whole S1 closure.'),indent=2)+'\n')
with tarfile.open(str(O)+'.tar.gz','w:gz') as t:
 for p in O.rglob('*'):
  if p.is_file():t.add(p,arcname=p.relative_to(O))
print(json.dumps(dict(files=len(files),archive=str(O)+'.tar.gz')))
