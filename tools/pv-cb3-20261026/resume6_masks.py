"""Generate a fixed P6 mask reference from the inspected row-link schedule.
The candidate requires independent shipped/reference Kani equality; this script
is neither proof nor runtime evidence.
"""
from pathlib import Path
import json,hashlib
root=Path(__file__).resolve().parents[2]
links=[]
for a,b in [(1,2),(2,3),(25,26),(27,28),(28,29),(30,31),(31,32)]:links.append((a*16+11,b*16))
links += [(11,28),(12,412),(44,428),(60,428),(44,960),(460,962),(508,964),(960,966),(962,966),(964,967),(966,967),(64,969),(865,969),(523,970),(475,540),(523,540),(970,528)]
for level in range(20):links += [((33+level)*16+11,(34+level)*16+12),((33+level)*16+11,(34+level)*16)]
links=[(a+48 if a>=864 else a,b+48 if b>=864 else b) for a,b in links]
for level in range(24):
 aux=912+16*(level//4)+[1,5,9,13][level%4]
 target=4+level if level<=20 else 33+level
 previous=3 if level==0 else (4+level-1 if level-1<=20 else 33+level-1)
 links += [(previous*16+11,aux),(aux+1,target*16+12),(aux+1,target*16)]
assert len(links)==136
rows=sorted({r for a,b in links for r in [a,b]});assert len(rows)==214
masks=[0]*64
for r in rows:masks[r//16] |= 1<<(r%16)
s='//! Fixed owned P6 reference. Independent native comparison required.\n'
s+='pub fn masks()->Result<[u16;64],aspis_statement::pool_v1::pair_tree_hiding::PoolV1PairHidingLayoutErrorV1>{\n Ok(['+','.join(map(str,masks))+'])\n}\n'
p=root/'tools/pv-cb3-20261026/resume6_mask_reference.rs';p.write_text(s)
e=root/'evidence/pv-cb3-20261026/RESUME6_MASK_CANDIDATE.json'
e.write_text(json.dumps(dict(status='candidate only; native association required',links=links,active_rows=rows,masks=masks,reference_sha256=hashlib.sha256(s.encode()).hexdigest()),indent=2)+'\n')
print('mask candidate',len(links),len(rows),masks)
