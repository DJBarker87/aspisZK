#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,shutil,tarfile
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');O=H/'s6-five-wide-export-v1';O.mkdir(exist_ok=False)
def copy(p,q):q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q)
P=H/'s6-full-forest-codec-five-unrolled-v1'
for p in (P/'wide-generated').rglob('*'):
 if p.is_file() and p.suffix in ['.lean','.json']:copy(p,O/'generated'/p.relative_to(P/'wide-generated'))
for tag in ['s6-full-forest-codec-five-unrolled-aeneas-wide-v1','s6-formatter-tool-build-v1']:
 for p in (H/'receipts'/tag).iterdir():
  if p.is_file():copy(p,O/'attempts'/tag/p.name)
 for suffix in ['input','admission']:copy(H/(tag+'-'+suffix+'.json'),O/'attempts'/tag/(suffix+'.json'))
W=H/'s6-formatter-tool-v2'
for name in ['input.json','receipt.json','candidate.patch','build.log','time.log','admission-global.json','admission-app-scopes.json']:copy(W/name,O/'formatter-tool'/name)
copy(W/'source/src/Translate.ml',O/'formatter-tool/Translate.ml')
copy(H/'s1-collapse-tool-recover-v2/source/src/Translate.ml',O/'formatter-tool/Translate.original.ml')
copy(H/'s6-formatter-tool-v1/formatter-only.json',O/'excluded-tool-setup/formatter-only.json')
for name in ['build-formatter-tool-host.py','format-five-codec-host.py','formatter-tool-host.py']:copy(H/name,O/'runners'/name)
files={str(p.relative_to(O)):hashlib.sha256(p.read_bytes()).hexdigest() for p in O.rglob('*') if p.is_file()}
(O/'manifest.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',files=files,qualification='Same source LLBC as five-loop extraction; formatting margin only. Generated templates diagnostic, no custom axioms imported. Tool setup failure excluded. Extraction is not a codec roundtrip or SDK proof.'),indent=2)+'\n')
with tarfile.open(str(O)+'.tar.gz','w:gz') as t:
 for p in O.rglob('*'):
  if p.is_file():t.add(p,arcname=str(p.relative_to(O)))
