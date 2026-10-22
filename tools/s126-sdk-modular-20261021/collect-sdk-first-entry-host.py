#!/usr/bin/env python3
"""Collect exact native first-entry cases, source/text only. May collect partial
progress; accepted coordinates enumerated explicitly. No whole S2 claim.
"""
from pathlib import Path
import json,hashlib,shutil,sys
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');O=H/sys.argv[1];O.mkdir(exist_ok=False)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def copy(p,r):
 q=O/r;q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q)
revision=sys.argv[2] if len(sys.argv)>2 else 'v2';assert revision in ['v1','v2']
versions=[f'first-entry-root0-window{i}-{revision}' for i in range(15)]+[f'first-entry-root1-{revision}',f'first-entry-root2-{revision}'];accepted={};pending=[]
for v in versions:
 tag='sdk-'+v;P=H/('sdk-shared-prefix-'+v);audit=H/tag/'entry-audit.json'
 if not audit.exists():pending.append(v);continue
 a=json.loads(audit.read_text());r=json.loads((H/'receipts'/tag/'receipt.json').read_text());i=json.loads((H/(tag+'-input.json')).read_text());assert r['exit_status']==10 and r['swaps']==0
 for rel in ['src/lib.rs','Cargo.toml','Cargo.lock','source-cut.json']:copy(P/rel,Path('sources')/v/rel)
 cg='sdk-shared-prefix-codegen-'+v
 for name in [tag,cg]:
  for suffix in ['-input.json','-admission.json','-dependency-postcheck.json']:
   p=H/(name+suffix)
   if p.exists():copy(p,name+suffix)
  for p in (H/'receipts'/name).iterdir():
   if p.suffix in ['.json','.log']:copy(p,Path('receipts')/name/p.name)
 for rel in ['runner-at-launch.py','source-cut.json','comparison-body.c','comparison-declaration.c','property-inventory.json','properties-complete.json','entry-audit.json','cbmc-exit.json']:
  p=H/tag/rel
  if p.exists():copy(p,Path('cases')/v/rel)
 raw=H/tag/('step'+str(len(i['commands'])-1)+'.log');copy(raw,Path('cases')/v/'all-properties.log')
 cginput=json.loads((H/(cg+'-input.json')).read_text())
 for package,pin in cginput['local_dependency_source_pins'].items():
  root=Path(pin['root'])
  for rel,d in pin['files'].items():
   assert sha(root/rel)==d;(copy(root/rel,Path('dependencies')/package/rel))
 accepted[v]=dict(noncover_successes=a['noncover_successes'],reached_covers=len(a['reached_covers']),receipt_sha256=sha(H/'receipts'/tag/'receipt.json'),source_sha256=sha(P/'src/lib.rs'),wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swaps=r['swaps'])
for n in ['run-modular-host.py','run-sdk-shared-prefix-host.py','audit-native-first-entry-host.py','run-native-first-entry-queue-host.py','run-native-first-entry-v2-queue-host.py','capped.py','reservation.py']:copy(H/'kit'/n,Path('runner')/n)
for worker in ['a','b']:
 for p in (H/f'sdk-first-entry-queue-{worker}-{revision}').iterdir():
  if p.suffix in ['.json','.log']:copy(p,Path('queues')/worker/p.name)
(O/'qualification.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',accepted=accepted,pending=pending,qualification=__doc__,remaining='Coordinate coverage is first-entry only under pure scan/comparison overapproximations and typed successful child cuts. No SDK models or owned reference. Actual source child/scan/gate installation, general valid runtime heap embedding, returned first and successful writeback/Drop/oracle composition still required.'),indent=2)+'\n')
(O/'manifest.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',files={str(p.relative_to(O)):sha(p) for p in O.rglob('*') if p.is_file()}),indent=2)+'\n')
print(json.dumps(dict(accepted=len(accepted),pending=len(pending),output=str(O))))
