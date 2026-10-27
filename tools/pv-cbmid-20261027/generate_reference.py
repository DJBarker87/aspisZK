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
# These literals are candidates until the complete Kani equations pass.
s='//! Owned P6 candidates. No shipped/reference association asserted here.\n'
s+='use aspis_statement::pool_v1::pair_tree_hiding::PoolV1PairHidingLayoutErrorV1 as Error;\n'
s+='pub fn masks()->Result<[u16;64],Error>{Ok(['+','.join(map(str,masks))+'])}\n'
s+='pub fn rows()->Result<alloc::vec::Vec<u16>,Error>{\nlet mut out=alloc::vec::Vec::new();\n'
for row in rows:s+='out.push('+str(row)+');\n'
s+='Ok(out)\n}\n'
s+=(root/'tools/pv-cbmid-20261027/reference_classifier.rs').read_text()
# Symbolic classifier determines the literal candidate. Kani is still required.
def aux(row,col):
 if row<912:return False
 if row<1008:return (row-912)%4==2 or ((row-912)%4==1 and col<=8)
 translated=row-48
 return any((translated==960+2*v or translated==961+2*v or translated==((960+2*v)^12)) and col<=10 for v in range(3)) or (translated==966 and col<3) or (translated==967 and col<2) or (translated==969 and col<=10) or (translated==970 and col<10)
cells=[(row,col) for col in range(16) for row in range(1024) if (row<912 and row%16>=13) or (row>=912 and not aux(row,col))]
assert len(cells)==3803
s+='pub fn cells()->Result<alloc::vec::Vec<aspis_statement::trace_v4::TraceCell>,Error>{\nlet mut out=alloc::vec::Vec::new();\n'
chunks=[cells[i:i+64] for i in range(0,len(cells),64)]
for i in range(len(chunks)):s+='out=cells_chunk_'+str(i)+'(out);\n'
s+='Ok(out)\n}\n'
for i,chunk in enumerate(chunks):
 s+='pub fn cells_chunk_'+str(i)+'(mut out:alloc::vec::Vec<aspis_statement::trace_v4::TraceCell>)->alloc::vec::Vec<aspis_statement::trace_v4::TraceCell>{\n'
 for row,col in chunk:s+='out.push(aspis_statement::trace_v4::TraceCell{row:'+str(row)+',column:'+str(col)+'});\n'
 s+='out\n}\n'
p=root/'tools/pv-cbmid-20261027/reference.rs';p.write_text(s)
e=root/'evidence/pv-cbmid-20261027/REFERENCE-CANDIDATE.json'
e.write_text(json.dumps(dict(status='candidate only; independent complete native association required',links=links,active_rows=rows,masks=masks,cells=cells,chunk_sizes=[len(c) for c in chunks],reference_sha256=hashlib.sha256(s.encode()).hexdigest()),indent=2)+'\n')
print('candidate',len(links),len(rows))
