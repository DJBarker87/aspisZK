#!/usr/bin/env python3
"""Reconcile every enabled property of actual source-site scan_enter DFCC check."""
from pathlib import Path
import json,hashlib,re
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');tag='sdk-native-scan-fission-enter-v1';O=H/tag;P=H/'sdk-shared-prefix-scan-fission-enter-v1';load=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
i=load(H/(tag+'-input.json'));r=load(H/'receipts'/tag/'receipt.json');assert r['exit_status']==10 and r['swaps']==0
h=i['harness_metadata'];assert h['attributes']['kind']=={'ProofForContract':{'target_fn':'scan_enter'}} and not h['attributes']['verified_stubs']
assert any('--enforce-contract' in cmd and h['contract']['contracted_function_name'] in cmd for cmd in i['commands'])
props=[p for item in load(O/'property-inventory.json') for p in item.get('properties',[])];expected={p['name']:p for p in props};assert len(expected)==len(props)
raw=O/('step'+str(len(i['commands'])-1)+'.log');current=None;block=[];rows=[]
for line in raw.read_text().splitlines():
 end=line.find('] ') if line.startswith('[') else -1
 while end>=0 and line[1:end] not in expected:end=line.find('] ',end+2)
 if end>=0:
  assert current is None;current=line[1:end];block=[line[end+2:]]
 elif current is not None:block.append(line)
 if current is not None:
  m=re.fullmatch(r'(.*): (SUCCESS|FAILURE|UNKNOWN|UNREACHABLE|NOT CHECKED|ERROR)','\n'.join(block),re.S)
  if m:rows.append(dict(property=current,description=m[1],status=m[2]));current=None;block=[]
assert current is None
actual={x['property']:x for x in rows};assert len(actual)==len(rows) and actual.keys()==expected.keys()
covers=[p['name'] for p in props if p['class']=='cover'];assert len(covers)==2
assert all(x['status']==('FAILURE' if x['property'] in covers else 'SUCCESS') for x in rows)
assert any(p['class']=='assigns' for p in props)
assert sha(P/'src/lib.rs')==i['source_sha256']
(O/'properties-complete.json').write_text(json.dumps(rows,indent=2)+'\n')
(O/'scan-enter-audit.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',source_sha256=i['source_sha256'],properties=len(props),noncover_successes=len(props)-2,reached_covers=covers,raw_goto_sha256=i['raw_goto_sha256'],prepared_goto_sha256=sha(O/'ready.out'),pins={str(p):sha(p) for p in [raw,O/'property-inventory.json',H/(tag+'-input.json'),H/'receipts'/tag/'receipt.json',Path(__file__)]},scope='Original scan_enter body at actual native scan site, empty enforced write footprint and every enabled assertion/safety/unwind check. Original SDK methods and complete statement retained. First entry stop; source any/comparison and child ports remain explicit. Not complete native caller or runtime correspondence.'),indent=2)+'\n')
print(json.dumps(dict(checks=len(props)-2,covers=len(covers))))
