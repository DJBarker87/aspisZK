#!/usr/bin/env python3
"""Source-only conditional successful reference constructor with exact cut pins."""
from pathlib import Path
import shutil,json,hashlib
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');O=H/'sdk-reference-first-export';O.mkdir(exist_ok=False)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def copy(p,r):
 q=O/r;q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q)
tag='sdk-reference-first-cut-v3';cg='sdk-shared-prefix-codegen-reference-first-v3';P=H/'sdk-shared-prefix-reference-first-v3';I=json.loads((H/(tag+'-input.json')).read_text());C=json.loads((H/(cg+'-input.json')).read_text())
for rel in ['src/lib.rs','Cargo.toml','Cargo.lock','source-cut.json']:copy(P/rel,Path('source')/rel)
for name in [tag,cg]:
 for suffix in ['-input.json','-admission.json','-dependency-postcheck.json']:
  p=H/(name+suffix)
  if p.exists():copy(p,name+suffix)
 for p in (H/'receipts'/name).iterdir():
  if p.suffix in ['.json','.log']:copy(p,Path('receipts')/name/p.name)
for rel in ['runner-at-launch.py','source-cut.json','comparison-body.c','comparison-declaration.c','property-inventory.json','properties-complete.json','reference-audit.json','cbmc-exit.json']:copy(H/tag/rel,Path('case')/rel)
copy(H/tag/('step'+str(len(I['commands'])-1)+'.log'),'case/all-properties.log')
for name,pin in C['local_dependency_source_pins'].items():
 root=Path(pin['root'])
 for rel,d in pin['files'].items():assert sha(root/rel)==d;copy(root/rel,Path('dependencies')/name/rel)
for n in ['run-reference-first-cut-host.py','run-modular-host.py','audit-reference-first-host.py','capped.py','reservation.py']:copy(H/'kit'/n,Path('runner')/n)
r=json.loads((H/'receipts'/tag/'receipt.json').read_text());a=json.loads((H/tag/'reference-audit.json').read_text());assert r['exit_status']==10 and r['swaps']==0 and a['noncover_successes']==4195
(O/'qualification.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',target=tag,receipt=r,noncover_successes=4195,reached_covers=2,qualification=__doc__,remaining='Reference success is conditional on native-derived metadata/counts/slots and same original buffers, admitted native-gate status0/tag2 image, source scan=false and installed typed successful child replies. Need general runtime/heap embedding, actual native child/refinement/effects/log/oracle composition, checkpoint writer/account/reader transport. Not whole S2 or TOTAL source closure.'),indent=2)+'\n')
(O/'manifest.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',files={str(p.relative_to(O)):sha(p) for p in O.rglob('*') if p.is_file()}),indent=2)+'\n')
print(O)
