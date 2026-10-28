"""Check the proposed sparse closed form against the frozen order source.
A disagreement is a checked copy-row counterexample: stop; do not repair it.
"""
from pathlib import Path
import hashlib,json,re
P=Path('crates/aspis-core/src/r0/transport_pads.rs');source=P.read_text()
pads=[int(x) for x in re.search(r'= \[(.*?)\];',source,re.S)[1].split(',') if x.strip()]
assert len(pads)==89 and len(set(pads))==89 and all(r<1023 and r!=1014 for r in pads)
order=pads+[r for r in range(1023) if r not in pads]+[1023]
def row(j):
 if j<89:return 16*(j//3)+13+j%3
 if j<479:return 16*((j-89)//13)+(j-89)%13
 return j
bad=[dict(index=j,original=r,copy=row(j)) for j,r in enumerate(order) if row(j)!=r]
record=dict(original_pads_sha256=hashlib.sha256(P.read_bytes()).hexdigest(),original_order_source_sha256=hashlib.sha256(Path('crates/aspis-core/src/r0/transport.rs').read_bytes()).hexdigest(),cells=len(order),counterexamples=bad,passed=not bad,status='compile-free source shape check only; native frozen-constant gate and Lean source equality still required',shape='89 pad cells; 390 complementary prefix cells; identity from index479')
Path('evidence/pv-batch2-20261027/batch2b/ROW-SHAPE.json').write_text(json.dumps(record,indent=2)+'\n')
assert not bad,bad
print('all1024 order-source cells match the proposed sparse closed form')
