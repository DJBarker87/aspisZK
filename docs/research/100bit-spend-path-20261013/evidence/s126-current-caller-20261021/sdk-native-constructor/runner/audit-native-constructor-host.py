#!/usr/bin/env python3
"""Audit the actual native constructor-ready checks; no solver replay."""
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
frames=[x for x in props if 'original SDK first-prefix byte equals initial input' in x['description']];assert len(frames)==1
version=tag.removeprefix('sdk-');P=H/('sdk-shared-prefix-'+version);cut=json.loads((P/'source-cut.json').read_text());assert cut['scan_fission']['original']=='checkpoint_data.iter().any(|byte| *byte != 0)'
source=(P/'src/lib.rs').read_text()
for description in ['native first derives all original reference metadata/key/owner preconditions','native first implies actual source scan returned false','native first derives original unmodified S2 tag image','native first implies the source guard comparison returned equal','actual scan iterator starts at original checkpoint root2','actual native scan input is the original checkpoint byte at every coordinate','source iterator fission has no destructor effect','native candidate coordinate is the actual common typed encoder result']:
 assert any(description in p['description'] for p in props),description
assert sha(P/'src/lib.rs')==i['source_sha256']==cut['source_sha256']
(O/'properties-complete.json').write_text(json.dumps(rows,indent=2)+'\n')
(O/'constructor-audit.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',properties=len(props),noncover_successes=len(props)-2,reached_covers=covers,source_cut=cut,pins={str(q):sha(q) for q in [p,raw,H/(tag+'-input.json'),H/'receipts'/tag/'receipt.json',P/'src/lib.rs',P/'source-cut.json',Path(__file__)]},qualification='Constructor-entry audit supersedes generic inherited runner prose. Source scan fission requires a noninterference/equivalence certificate; this report does not supply one. Original SDK, one initial byte coordinate and typed/counter/slot facts at first entry only. No returned first result, post-frame or termination. Pure scan/comparison overapproximation and typed child cuts require actual source/runtime/caller installation; not whole S2.'),indent=2)+'\n')
print(json.dumps(dict(tag=tag,noncover_successes=len(props)-2,reached_covers=2)))
