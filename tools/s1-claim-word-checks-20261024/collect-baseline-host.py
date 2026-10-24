#!/usr/bin/env python3
from pathlib import Path
import json,hashlib,shutil,tarfile
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');S=H/'s1-claim-owned-nested-v10';W=H/'s1-borrowed-helper-baseline-v1-20261024';O=H/'s1-borrowed-helper-baseline-source-only-v1';O.mkdir(exist_ok=False)
def copy(p,q):q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q)
for root,dest in [(W,'baseline'),(S/'input','input'),(S/'generated','historical-generated')]:
 for p in root.rglob('*'):
  if p.is_file() and not any(n in ['target','.git'] for n in p.relative_to(root).parts) and p.suffix in ['.rs','.lean','.toml','.lock','.json','.log']:
   copy(p,O/dest/p.relative_to(root))
for phase in ['charon','aeneas']:
 name='s1-claim-owned-nested-'+phase+'-v10';r=H/'receipts'/name
 for p in r.iterdir():
  if p.is_file() and p.suffix in ['.json','.log']:copy(p,O/'historical-attempts'/name/p.name)
 for suffix in ['input','admission']:
  p=H/(name+'-'+suffix+'.json')
  if p.is_file():copy(p,O/'historical-attempts'/name/(suffix+'.json'))
copy(S/'source-change.json',O/'source-change.json')
copy(H/'extract-borrowed-baseline-host.py',O/'baseline-runner.py')
files={str(p.relative_to(O)):hashlib.sha256(p.read_bytes()).hexdigest() for p in O.rglob('*') if p.is_file()}
(O/'manifest.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',files=files,qualification='Pinned original baseline Aeneas translation, exact retained source kit, reused Charon and excluded historical patched-tool translation. Generated external templates are unimported raw source, not accepted axioms. LLBC and binaries are hash-pinned only.'),indent=2)+'\n')
with tarfile.open(str(O)+'.tar.gz','w:gz') as t:
 for p in O.rglob('*'):
  if p.is_file():t.add(p,arcname=p.relative_to(O))
print(json.dumps(dict(files=len(files),archive=str(O)+'.tar.gz')))
