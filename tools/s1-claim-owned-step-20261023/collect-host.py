#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,shutil,tarfile,sys
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021')
tag,kit,export=sys.argv[1:4] if len(sys.argv)>1 else ('s1-original-owned-step-v1','aspis-s1-claim-owned-step-v1','s1-claim-owned-step-export-v1')
O=H/export;O.mkdir(exist_ok=False)
def copy(p,q):
    q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q)
assert json.loads((H/'receipts'/tag/'receipt.json').read_text())['exit_status']==0
for p in (H/'receipts'/tag).iterdir():
    if p.is_file() and p.suffix in ['.json','.log']:copy(p,O/'attempt'/p.name)
for suffix in ['input','admission','all-local-before','all-local-after','dependency-postcheck']:
    copy(H/(tag+'-'+suffix+'.json'),O/'attempt'/(suffix+'.json'))
root=H/kit
for p in root.rglob('*'):
    if p.is_file() and not any(x in ['target','.git'] for x in p.relative_to(root).parts) and p.suffix in ['.rs','.toml','.lock','.json']:
        copy(p,O/'input'/p.relative_to(root))
copy(H/'s1-run-replay-host.py',O/'runner.py')
files={str(p.relative_to(O)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(O.rglob('*')) if p.is_file()}
(O/'manifest.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',files=files,
    qualification='Native source one-step coupling on complete carriers, with explicit shared arbitrary push and field ports. No whole-source/caller refinement claim; actual leaf interpretation and admitted parser-frame contract remain explicit.'),indent=2)+'\n')
with tarfile.open(str(O)+'.tar.gz','w:gz') as t:
    for p in O.rglob('*'):
        if p.is_file():t.add(p,arcname=str(p.relative_to(O)))
print(json.dumps(dict(files=len(files),archive=str(O)+'.tar.gz')))
