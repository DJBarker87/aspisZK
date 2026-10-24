#!/usr/bin/env python3
"""Retain old/new ownership proposals for every changed MIR body occurrence."""
import collections,json
from pathlib import Path
H=Path('/home/dombarker/project-offloads/codex-cx-s10-repin3-20261023');P=H.parent/'codex-cx-s10-repin2-20261023'
index=[]
for root in [P,H]:
 d=collections.defaultdict(list)
 for line in (root/'declaration-owners.jsonl').open():
  r=json.loads(line);d[(r['mode'],r['body_sha256'])].append(r)
 index.append(d)
rows=[]
for m in json.loads((H/'mir-diff.json').read_text())['modes']:
 for r in m['changed']:
  sides={}
  for i,side in enumerate(['old','new']):
   sides[side]=[]
   for b in r[side]:
    matches=index[i][(m['mode'],b['sha256'])];assert matches,(m['mode'],r['key'],side)
    sides[side].extend(matches)
  rows.append(dict(mode=m['mode'],key=r['key'],status=r['status'],**sides))
x=dict(records=rows,scope='Existing disjoint policy and lead overlay proposals for each old/new body occurrence. No owner acceptance, source semantics or final reachable-instance correspondence supplied.',complete=False)
(H/'changed-declaration-ownership.json').write_text(json.dumps(x,indent=2,sort_keys=True)+'\n')
print('changed ownership groups',len(rows))
