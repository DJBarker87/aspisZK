#!/usr/bin/env python3
"""Reconcile complete entry-only report with saved exact enabled inventory; no replay."""
from pathlib import Path
import json,hashlib,re,sys
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');tag=sys.argv[1];O=H/tag
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
i=json.loads((H/(tag+'-input.json')).read_text());r=json.loads((H/'receipts'/tag/'receipt.json').read_text())
assert r['exit_status']==10 and r['swaps']==0
assert i['harness_metadata']['attributes']['kind']=='Proof'
assert not any('sdk_live_models' in str(x) for x in i['harness_metadata']['attributes'].get('stubs',[]))
p=O/'property-inventory.json';props=[x for a in json.loads(p.read_text()) for x in a.get('properties',[])];expected={x['name']:x for x in props};assert len(expected)==len(props)
raw=O/('step'+str(len(i['commands'])-1)+'.log');rows=[];current=None;block=[]
for line in raw.read_text().splitlines():
 end=line.find('] ') if line.startswith('[') else -1
 while end>=0 and line[1:end] not in expected:end=line.find('] ',end+2)
 if end>=0:
  assert current is None;current=line[1:end];block=[line[end+2:]]
 elif current is not None:block.append(line)
 if current is not None:
  match=re.fullmatch(r'(.*): (SUCCESS|FAILURE|UNKNOWN|UNREACHABLE|NOT CHECKED|ERROR)','\n'.join(block),re.S)
  if match:rows.append(dict(property=current,description=match[1],status=match[2]));current=None;block=[]
assert current is None
actual={x['property']:x for x in rows};assert len(actual)==len(rows) and actual.keys()==expected.keys()
covers=[x['name'] for x in props if x['class']=='cover'];assert len(covers)==2
assert all(x['status']==('FAILURE' if x['property'] in covers else 'SUCCESS') for x in rows)
version=tag.removeprefix('sdk-native-');P=H/('sdk-shared-prefix-'+version);cut=json.loads((P/'source-cut.json').read_text())
assert 'NECESSARY reached-first image' in cut['qualification']
assert sha(P/'src/lib.rs')==i['source_sha256']==cut['source_sha256']
(O/'properties-complete.json').write_text(json.dumps(rows,indent=2)+'\n')
(O/'pair-audit.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',properties=len(props),noncover_successes=len(props)-2,reached_covers=covers,source_cut=cut,pins={str(q):sha(q) for q in [p,raw,H/(tag+'-input.json'),H/'receipts'/tag/'receipt.json',P/'src/lib.rs',P/'source-cut.json',Path(__file__)]},qualification='Paired first-entry check on normalized NECESSARY image only. Both complete native and borrowed-reference bodies, actual SDK and common typed cuts. Native first implies reference first with original byte pointers/public projection/k/None and matching empty-result error. Normalization identity, actual source child/scan/gate interpretation, arbitrary continuation and complete return/runtime/oracle/TX2 transport remain; not whole S2.'),indent=2)+'\n')
print(json.dumps(dict(tag=tag,noncover_successes=len(props)-2,reached_covers=2)))
