#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,shutil,tarfile
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');P=H/'s6-full-forest-codec-extract-v3';O=H/'s6-forest-codec-extraction-export-v1';O.mkdir(exist_ok=False)
def copy(p,q):q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q)
for p in P.rglob('*'):
 if p.is_file() and not any(x in ['target','.git'] for x in p.relative_to(P).parts) and p.suffix in ['.rs','.lean','.toml','.lock','.json']:
  copy(p,O/'source'/p.relative_to(P))
for n,out in [('Codec.llbc','original.llbc.json'),('Codec-renamed.llbc','renamed.llbc.json')]:copy(P/n,O/'llbc'/out)
for tag in ['s6-full-forest-codec-charon-v3','s6-full-forest-codec-aeneas-v3','s6-full-forest-codec-aeneas-renamed-v1']:
 for p in (H/'receipts'/tag).iterdir():
  if p.is_file():copy(p,O/'attempts'/tag/p.name)
 for suffix in ['input','admission']:copy(H/(tag+'-'+suffix+'.json'),O/'attempts'/tag/(suffix+'.json'))
for n in ['s6-full-forest-extract-codec-host.py','s6-rename-codec-host.py']:copy(H/n,O/'runners'/n)
files={str(p.relative_to(O)):hashlib.sha256(p.read_bytes()).hexdigest() for p in O.rglob('*') if p.is_file()}
(O/'manifest.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',files=files,qualification='Actual native outer full-forest encoder and current boxed decoder extracted with nine explicit nested children. Unrenamed Aeneas name collision excluded. Metadata-only constructor backend names changed; all bodies/IDs/types/Rust names identical. Raw templates are diagnostic, not imported. No child closure or native SDK/runtime execution theorem.'),indent=2)+'\n')
with tarfile.open(str(O)+'.tar.gz','w:gz') as t:
 for p in O.rglob('*'):
  if p.is_file():t.add(p,arcname=str(p.relative_to(O)))
print(json.dumps(dict(files=len(files),archive=str(O)+'.tar.gz')))
