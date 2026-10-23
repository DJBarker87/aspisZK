#!/usr/bin/env python3
"""Export only source/text evidence; never tool/model/build binaries."""
from pathlib import Path
import shutil,json,hashlib,tarfile
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');O=H/'s1-claim-source-steps-export-v1';O.mkdir(exist_ok=False)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def copy(p,d):
 d.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,d)
tags=['s1-claim-step-actual-v1','s1-claim-step-actual-v2','s1-claim-step-actual-v3','s1-claim-selector-actual-v1','s1-claim-selector-y1-v1','s1-claim-step-coupled-v1','s1-push-stub-result-preflight-v1','s1-push-stub-result-preflight-v2','s1-push-maperr-result-preflight-v1','s1-push-maperr-mir0-v1','s1-claim-step-coupled-mir0-v1','s1-claim-step-coupled-strict-v2','s1-claim-step-coupled-strict-v3']
for tag in tags:
 p=H/'receipts'/tag
 if p.exists():
  for f in p.iterdir():
   if f.is_file() and f.suffix in ['.json','.log']:copy(f,O/'attempts'/tag/f.name)
 for suffix in ['input','admission','dependency-postcheck','all-local-before','all-local-after','stopped']:
  f=H/(tag+'-'+suffix+'.json')
  if f.exists():copy(f,O/'attempts'/tag/(suffix+'.json'))
for n in [2,3,4,5,7,8,9,10,11,12]:
 p=H/f'aspis-s1-claim-source-steps-v{n}'
 for rel in ['src/lib.rs','src/fast_pairing.rs','src/proofs.rs','Cargo.toml','Cargo.lock','source-binding.json','source-preflight.json']:
  f=p/rel
  if f.exists():copy(f,O/'inputs'/f'v{n}'/rel)
common=H/'aspis-s1-claim-source-steps-v12/frozen-probe'
for f in common.rglob('*'):
 if f.is_file() and f.suffix in ['.rs','.toml','.lock']:copy(f,O/'dependency/frozen-probe'/f.relative_to(common))
for n in [1,2]:
 p=H/f's1-claim-scalar-helper-v{n}'
 for rel in ['input/lib.rs','input/Cargo.toml','input/Cargo.lock','source-change.json']:
  f=p/rel
  if f.exists():copy(f,O/'excluded-extractor'/f'v{n}'/rel)
 f=p/'ClaimScalar.llbc'
 if f.exists():copy(f,O/'excluded-extractor'/f'v{n}'/'ClaimScalar.llbc.json')
 for phase in ['charon','aeneas']:
  tag=f's1-claim-scalar-helper-{phase}-v{n}'
  for f in (H/'receipts'/tag).iterdir():
   if f.is_file() and f.suffix in ['.json','.log']:copy(f,O/'excluded-extractor'/f'v{n}'/phase/f.name)
  for suffix in ['input','admission']:
   copy(H/(tag+'-'+suffix+'.json'),O/'excluded-extractor'/f'v{n}'/phase/(suffix+'.json'))
for name in ['kit/run-modular-host.py','s1-run-mir0-host.py','s1-run-strict-host.py']:
 copy(H/name,O/'runners'/Path(name).name)
files={str(f.relative_to(O)):sha(f) for f in sorted(O.rglob('*')) if f.is_file()}
(O/'manifest.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',qualification='One-step source/call-coupling evidence and diagnostic history, not whole original claim/source equivalence. All opaque field/push interpretations remain explicit. No binaries.',files=files),indent=2)+'\n')
with tarfile.open(str(O)+'.tar.gz','w:gz') as t:
 for f in O.rglob('*'):
  if f.is_file():t.add(f,arcname=str(f.relative_to(O)))
print(json.dumps(dict(files=len(files),bytes=sum(f.stat().st_size for f in O.rglob('*') if f.is_file()),archive=str(O)+'.tar.gz')))
