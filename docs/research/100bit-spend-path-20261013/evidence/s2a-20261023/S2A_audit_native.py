#!/usr/bin/env python3
"""Audit plain CBMC output, including multi-line descriptions and Kani probes.
Reachability assertions encode negated reachability: FAILURE is evidence of
reach, not a failed safety assertion. Covers likewise use FAILURE for reach.
No proof credit is assigned to unparsed or missing properties.
"""
from pathlib import Path
import json,re,sys,collections,hashlib
p=Path(sys.argv[1]); props={r['name']:r for i in json.loads((p/'properties.json').read_text()) for r in i.get('properties',[])}
rows=[];current=None;block=[]
for line in (p/'step-9.log').read_text().splitlines():
 end=line.find('] ') if line.startswith('[') else -1
 while end>=0 and line[1:end] not in props:end=line.find('] ',end+2)
 if end>=0:
  assert current is None,('unfinished property',current,block)
  current=line[1:end];block=[line[end+2:]]
 elif current is not None:block.append(line)
 if current is not None:
  m=re.fullmatch(r'(.*): (SUCCESS|FAILURE|UNKNOWN|UNREACHABLE|NOT CHECKED|ERROR)','\n'.join(block),re.S)
  if m:rows.append(dict(name=current,description=m[1],status=m[2],kind=props[current]['class']));current=None;block=[]
assert current is None and len(rows)==len(props), (len(rows),len(props),current)
assert len(rows)==len({r['name'] for r in rows})
required=[r for r in rows if r['kind'] not in ['cover','reachability_check']]
covers=[r for r in rows if r['kind']=='cover'];probes=[r for r in rows if r['kind']=='reachability_check']
assert all(r['status']=='SUCCESS' for r in required),[r for r in required if r['status']!='SUCCESS']
assert len(covers)==2 and all(r['status']=='FAILURE' for r in covers),covers
assert all(r['status'] in ['SUCCESS','FAILURE'] for r in probes),probes
out={'schema':'focused-extractor-proof-packet-v1','scope':'native FIRST-ENTRY only; open pure typed child/scan/comparison ports, no production runtime certificate','required_properties':len(required),'required_failures':0,'reached_entry_covers':covers,'reachability_probes':len(probes),'reached_probes':sum(r['status']=='FAILURE' for r in probes),'raw_cbmc_exit':json.loads((p/'cbmc-exit.json').read_text())['exit_status'],'property_counts':dict(collections.Counter(r['kind'] for r in rows)),'pins':{f:hashlib.sha256((p/f).read_bytes()).hexdigest() for f in ['properties.json','step-9.log','inputs.json','cbmc-exit.json']}}
(p/'audit.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
