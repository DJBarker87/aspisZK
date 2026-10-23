#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,shutil,tarfile
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');O=H/'s6-std-options-export-v1';O.mkdir(exist_ok=False)
def copy(p,q):q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q)
P=H/'s6-std-option-methods-extract-v1'
for p in P.rglob('*'):
 if p.is_file() and not any(x in ['target','.git'] for x in p.relative_to(P).parts) and p.suffix in ['.lean','.rs','.toml','.lock','.json','.llbc']:
  copy(p,O/'source'/p.relative_to(P))
for tag in ['s6-std-option-methods-charon-v1','s6-std-option-methods-aeneas-v2','s6-std-methods-charon-v2','s6-std-methods-aeneas-v2','s6-full-forest-codec-full-std-charon-v1','s6-full-forest-codec-full-std-charon-v2']:
 for p in (H/'receipts'/tag).iterdir():
  if p.is_file():copy(p,O/'attempts'/tag/p.name)
 for suffix in ['input','admission','global-admission']:
  p=H/(tag+'-'+suffix+'.json')
  if p.is_file():copy(p,O/'attempts'/tag/(suffix+'.json'))
for tag in ['s6-std-methods-charon-v1','s6-std-option-methods-aeneas-v1','s6-full-forest-codec-full-std-aeneas-v1']:
 p=H/(tag+'-global-admission.json')
 if p.is_file():copy(p,O/'excluded-admission'/(tag+'.json'))
for folder in ['s6-std-methods-extract-v1','s6-full-forest-codec-full-std-v1']:
 P=H/folder
 for p in (P/'input').iterdir():
  if p.is_file() and p.suffix in ['.rs','.toml','.lock']:copy(p,O/'excluded-source'/folder/'input'/p.name)
 for n in ['Std.llbc','Codec.llbc']:
  p=P/n
  if p.is_file():copy(p,O/'excluded-source'/folder/(n+'.json'))
for name in ['extract-std-options-host.py','extract-std-options-aeneas-v2-host.py','extract-std-methods-host.py','extract-std-methods-v2-host.py','extract-full-std-host.py','extract-full-std-v2-host.py','rename-full-std-host.py']:copy(H/name,O/'runners'/name)
files={str(p.relative_to(O)):hashlib.sha256(p.read_bytes()).hexdigest() for p in O.rglob('*') if p.is_file()}
(O/'manifest.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',files=files,qualification='Actual generic Rust Option methods extracted with no external template. Earlier generic slice-array extraction hits PtrMetadata and is EXCLUDED. Whole native codec/std/SDK and roundtrip are not established by this packet.'),indent=2)+'\n')
with tarfile.open(str(O)+'.tar.gz','w:gz') as t:
 for p in O.rglob('*'):
  if p.is_file():t.add(p,arcname=str(p.relative_to(O)))
