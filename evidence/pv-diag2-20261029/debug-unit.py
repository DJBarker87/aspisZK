"""Bounded-size MIR body inspection for the deployed unit Error formatter."""
from pathlib import Path
import re,json,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-diag2-20261029');P=D.parent/'codex-pv-rdea-20261028';T=P/'client-target/release/deps'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pins=json.loads((P/'ir-mir-pins.json').read_text());rows=[]
for pin in pins['mir']:
 p=Path(pin['path'])
 if not p.name.startswith('aspis_r1_cost_probe-'):continue
 assert sha(p)==pin['sha256']
 # Keep the complete formatter CFG, not just a list of diagnostic names.
 cur=[];selected=False;start=0
 with p.open() as f:
  for n,line in enumerate(f,1):
   if line.startswith('fn '):
    if selected:rows.append(dict(path=str(p),sha256=sha(p),line=start,body=''.join(cur)))
    selected=('::fmt(' in line and '_1: &verifier::Error,' in line)
    cur=[];start=n
   if selected:cur.append(line)
  if selected:rows.append(dict(path=str(p),sha256=sha(p),line=start,body=''.join(cur)))
assert rows,'no deployed Error Debug formatter body found'
expected=['Parse','Semantic','Transcript','Relation','Merkle','Query','Checkpoint','Allocation','Rejected','AttemptsExhausted','Entropy']
for row in rows:
 body=row['body'];row['variant_literals']=[s for s in re.findall(r'const "([A-Za-z]+)"',body) if s in expected]
 # Bodies include generated promoted constants separately; retain all source
 # blocks. The formatter must choose a literal, not format field operands.
 row['formatter_write_str']='write_str' in body
 row['has_operand_debug_call']=bool(re.search(r'<(?!.*verifier).* as Debug>::fmt',body))
assert len(rows)==1 and sorted(rows[0]['variant_literals'])==sorted(expected) and rows[0]['formatter_write_str']
assert not rows[0]['has_operand_debug_call']
(D/'debug-unit-binding.json').write_text(json.dumps(dict(classification='complete selected MIR formatter body inspection; generic derivation/compiler mapping stays within existing compiler boundary',expected_variants=expected,rows=rows),indent=2)+'\n')
print('formatter bodies',len(rows),'direct literal sets',[r['variant_literals'] for r in rows])
