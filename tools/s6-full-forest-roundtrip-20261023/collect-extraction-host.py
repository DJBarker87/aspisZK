#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,shutil,subprocess,tarfile
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');O=H/'s6-forest-encoder-extraction-export-v1';O.mkdir(exist_ok=False)
def copy(p,q):q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q)
for v in [1,2]:
 P=H/f's6-full-forest-encoder-extract-v{v}';D=O/('excluded-wrapper-only' if v==1 else 'included-encoder')
 for p in P.rglob('*'):
  if p.is_file() and not any(x in ['target','.git'] for x in p.relative_to(P).parts) and p.suffix in ['.rs','.lean','.toml','.lock','.json']:
   copy(p,D/'source'/p.relative_to(P))
 for phase in ['charon','aeneas']:
  tag=f's6-full-forest-encoder-{phase}-v{v}'
  for p in (H/'receipts'/tag).iterdir():
   if p.is_file():copy(p,D/phase/p.name)
  for suffix in ['input','admission']:copy(H/(tag+'-'+suffix+'.json'),D/phase/(suffix+'.json'))
 for n in ['Encoder.llbc']:
  p=P/n;copyhash={'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()};(D/'llbc-pin.json').write_text(json.dumps(copyhash,indent=2)+'\n')
for n in ['s6-full-forest-extract-host.py','s6-full-forest-extract-included-host.py']:copy(H/n,O/'runners'/n)
rustc=Path('/home/dombarker/.rustup/toolchains/nightly-2026-06-01-x86_64-unknown-linux-gnu/bin/rustc')
(O/'toolchain.json').write_text(json.dumps(dict(rustc_sha256=hashlib.sha256(rustc.read_bytes()).hexdigest(),rustc_version=subprocess.check_output([str(rustc),'--version','--verbose'],text=True)),indent=2)+'\n')
files={str(p.relative_to(O)):hashlib.sha256(p.read_bytes()).hexdigest() for p in O.rglob('*') if p.is_file()}
(O/'manifest.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',files=files,qualification='Wrapper-only attempt excluded. Included outer encoder body is extracted with exactly five named opaque nested child functions. Raw axiom templates/resource-option output is diagnostic only; not imported. No child closure, Lean proof or native SDK/source execution theorem.'),indent=2)+'\n')
with tarfile.open(str(O)+'.tar.gz','w:gz') as t:
 for p in O.rglob('*'):
  if p.is_file():t.add(p,arcname=str(p.relative_to(O)))
print(json.dumps(dict(files=len(files),archive=str(O)+'.tar.gz')))
