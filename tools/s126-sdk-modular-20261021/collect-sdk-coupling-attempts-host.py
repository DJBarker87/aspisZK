#!/usr/bin/env python3
"""Retain unsuccessful coupling/constructor attempts, source/text only. No proof credit."""
from pathlib import Path
import json,hashlib,shutil
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');O=H/'sdk-coupling-attempts-export';O.mkdir(exist_ok=False)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def copy(p,r):
 q=O/r;q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q)
rows={}
for tag,crate in [('sdk-first-coupling-frame-v1','sdk-shared-prefix-first-coupling-v1'),('sdk-first-coupling-frame-v2','sdk-shared-prefix-first-coupling-v2'),('sdk-first-coupling-ordinary-native-v3','sdk-shared-prefix-first-coupling-v3'),('sdk-first-coupling-ordinary-models-v4','sdk-shared-prefix-first-coupling-v4'),('sdk-first-frame-root0-window0-v1','sdk-shared-prefix-first-frame-root0-window0-v1'),('sdk-reference-first-check-v1','sdk-reference-first-v1')]:
 P=H/crate
 for p in P.rglob('*'):
  if p.is_file() and ('target' not in p.relative_to(P).parts) and p.suffix in ['.rs','.toml','.lock','.json']:copy(p,Path('sources')/crate/p.relative_to(P))
 for suffix in ['-input.json','-admission.json','-dependency-postcheck.json']:
  p=H/(tag+suffix)
  if p.exists():copy(p,tag+suffix)
 for p in (H/'receipts'/tag).iterdir():
  if p.suffix in ['.json','.log']:copy(p,Path('receipts')/tag/p.name)
 if (H/tag).is_dir():
  for p in (H/tag).iterdir():
   if p.is_file() and p.suffix in ['.json','.log','.c','.py']:copy(p,Path('attempts')/tag/p.name)
 r=json.loads((H/'receipts'/tag/'receipt.json').read_text());assert r['exit_status']!=0
 rows[tag]=dict(crate=crate,receipt=r,status='excluded_no_proof_credit',reason='Solver deadline; do not repeat unchanged or increase cap. Reference v1 also contains checkpoint pointer preservation assertion incompatible with owned Vec replacement; corrected in v2.')
(O/'qualification.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',attempts=rows,qualification=__doc__),indent=2)+'\n')
(O/'manifest.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',files={str(p.relative_to(O)):sha(p) for p in O.rglob('*') if p.is_file()}),indent=2)+'\n')
print(O)
