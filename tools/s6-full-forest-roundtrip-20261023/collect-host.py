#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,shutil,sys,tarfile
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021')
tag,kit,export,runner=sys.argv[1:5];O=H/export;O.mkdir(exist_ok=False)
def copy(p,q):q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q)
for p in (H/'receipts'/tag).iterdir():
 if p.is_file() and p.suffix in ['.json','.log']:copy(p,O/'attempt'/p.name)
for suffix in ['input','admission','all-local-before','all-local-after','dependency-postcheck']:
 copy(H/(tag+'-'+suffix+'.json'),O/'attempt'/(suffix+'.json'))
for p in (H/kit).rglob('*'):
 if p.is_file() and not any(x in ['target','.git'] for x in p.relative_to(H/kit).parts) and p.suffix in ['.rs','.toml','.lock','.json']:
  copy(p,O/'input'/p.relative_to(H/kit))
copy(H/runner,O/'runner.py')
rec=json.loads((O/'attempt/receipt.json').read_text())
files={str(p.relative_to(O)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(O.rglob('*')) if p.is_file()}
(O/'manifest.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',files=files,exit_status=rec['exit_status'],qualification='Native frozen complete-carrier source evidence only; exact scope and failed/successful status retained. No whole S1/S6/SDK closure or coherent release replay.'),indent=2)+'\n')
with tarfile.open(str(O)+'.tar.gz','w:gz') as t:
 for p in O.rglob('*'):
  if p.is_file():t.add(p,arcname=str(p.relative_to(O)))
print(json.dumps(dict(files=len(files),archive=str(O)+'.tar.gz')))
