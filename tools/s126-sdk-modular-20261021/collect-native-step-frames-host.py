#!/usr/bin/env python3
"""Collect actual direct cleanup and region bindings; exclude failed predecessors."""
from pathlib import Path
import json,hashlib,shutil,tomllib,re
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');O=H/'sdk-native-step-frames-export-v1';O.mkdir(exist_ok=True)
load=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def copy(p,r):
 q=O/r;q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q)
cases=[('sdk-ordered-cleanup-frame-check-v1','sdk-ordered-cleanup-frame-v1',False),('sdk-ordered-cleanup-stack-frame-check-v1','sdk-ordered-cleanup-stack-frame-v1',False),('sdk-ordered-cleanup-direct-frame-check-v1','sdk-ordered-cleanup-direct-frame-v1',True),('sdk-cleanup-region-bindings-check-v1','sdk-cleanup-region-bindings-v1',False),('sdk-cleanup-region-bindings-check-v2','sdk-cleanup-region-bindings-v2',True),('sdk-native-initial-snapshot-pair-v1','sdk-shared-prefix-initial-snapshot-pair-v1',False),('sdk-shared-prefix-codegen-initial-snapshot-pair-v1','sdk-shared-prefix-initial-snapshot-pair-v1',False)]
rows={}
for tag,source,accept in cases:
 P=H/source;i=load(H/(tag+'-input.json'));r=load(H/'receipts'/tag/'receipt.json');assert sha(P/'src/lib.rs')==i['source_sha256']
 for rel in ['src/lib.rs','src/sdk_live_models.rs','Cargo.toml','Cargo.lock','source-cut.json']:
  if (P/rel).exists():copy(P/rel,Path('sources')/source/rel)
 for suffix in ['-input.json','-admission.json','-dependency-postcheck.json']:
  p=H/(tag+suffix)
  if p.exists():copy(p,tag+suffix)
 for p in (H/'receipts'/tag).iterdir():
  if p.suffix in ['.json','.log']:copy(p,Path('receipts')/tag/p.name)
 if (H/tag).is_dir():
  for p in (H/tag).iterdir():
   if p.is_file() and p.suffix in ['.json','.log','.c','.py']:copy(p,Path('cases')/tag/p.name)
 row=dict(accepted=accept,source=source,source_sha256=sha(P/'src/lib.rs'),receipt=r)
 if accept:
  assert r['exit_status']==0 and r['swaps']==0
  log=(H/'receipts'/tag/'stdout.log').read_text();n=re.search(r'0 of (\d+) failed',log);assert n and '2 of 2 cover properties satisfied' in log
  name=i['command'][i['command'].index('--harness')+1];crate=tomllib.loads((P/'Cargo.toml').read_text())['package']['name'].replace('-','_');matches=[]
  for p in (H/'target/kani').rglob(crate+'*.kani-metadata.json'):
   for h in load(p)['proof_harnesses']:
    if h['pretty_name']==name:matches.append((p,h))
  assert len(matches)==1;p,h=matches[0];copy(p,Path('metadata')/tag/'harness-metadata.json');raw=Path(h['goto_file']);ready=Path(str(raw).replace('.symtab.out','.out'))
  row.update(noncover_successes=int(n[1]),reached_covers=2,harness=name,raw_goto_sha256=sha(raw),prepared_goto_sha256=sha(ready))
 pins=i.get('local_dependency_source_pins',{})
 for package,pin in pins.items():
  for rel,d in pin['files'].items():assert sha(H/'sdk-release-allocator-export-v1/dependencies'/package/rel)==d
 rows[tag]=row
for tag in ['sdk-cleanup-stack-loop-inventory-v1','sdk-native-cleanup-goto-inventory-v1']:
 for rel in ['receipt.json','time.log','stderr.log']:copy(H/'receipts'/tag/rel,Path('receipts')/tag/rel)
 if 'loop' in tag:copy(H/'receipts'/tag/'stdout.log',Path('receipts')/tag/'stdout.log')
 for suffix in ['-input.json','-admission.json']:copy(H/(tag+suffix),tag+suffix)
for p in (H/'sdk-native-cleanup-order-v1').iterdir():
 if p.is_file():copy(p,Path('cleanup-order')/p.name)
for n in ['run-modular-host.py','run-sdk-shared-prefix-host.py','capped.py','reservation.py','inspect-cleanup-loops-host.py','inspect-native-cleanup-host.py','certify-native-cleanup-order-host.py']:copy(H/'kit'/n,Path('runner')/n)
(O/'qualification.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',targets=rows,dependency_evidence='../sdk-release-allocator/dependencies',scope='Full actual guard/Box/Vec destruction sequence is checked counter-only, with actual destructor bodies and only the explicit frozen Bump deallocation shim. Actual SDK regions bind copy/counter footprints away from all data/protected metadata. Actual native compiled successful post-copy order is separately inspected and matches the five typed drop roles. Kernel footprint rules compose these step-level frame observations.',remaining='Source typed-value relocation/drop-glue semantics and general source/runtime/ABI/allocator interpretation remain explicit; the finite GOTO certificate establishes order/control, not an independent Rust semantics theorem. Complete fixed-initial native caller/installed source child/oracle/TX2 binding and S1/S6 still open. Both prior nested-cleanup checks and initial-clone paired query timed out and are excluded; no cap increase.'),indent=2)+'\n')
(O/'manifest.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',files={str(p.relative_to(O)):sha(p) for p in O.rglob('*') if p.is_file() and p.name!='manifest.json'}),indent=2)+'\n');print(json.dumps(dict(output=str(O),accepted=sum(x['accepted'] for x in rows.values()),excluded=sum(not x['accepted'] for x in rows.values()))))
