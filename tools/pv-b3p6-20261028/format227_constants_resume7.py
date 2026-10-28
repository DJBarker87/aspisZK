"""Exhaustively inspect immutable table fields guarding the five shipped LLVM panics.
This is a finite constant-table structural check, not a field arithmetic differential.
"""
from pathlib import Path
import json,re,hashlib
D=Path('evidence/pv-b3p6-20261028/resume7');p=Path('crates/aspis-r1-cost-probe/src/host_copy_terminal_constants.rs');raw=p.read_bytes();s=raw.decode()
a=s.split('const COPY_PATTERNS:',1)[1].split('const COPY_LINKS:',1)[0]
patterns=[]
for i,line in enumerate(l for l in a.splitlines()if 'CompiledPoolV1PairForestPattern {'in l):
 cols=[int(x)for x in re.search(r'columns: \[([^]]+)\]',line)[1].split(',')]
 assert len(cols)==16 and all(0<=c<16 for c in cols)
 patterns.append(dict(index=i,columns=cols,max_column=max(cols),safe=True))
links=[]
for i,line in enumerate(l for l in s.splitlines()if 'CompiledPoolV1PairForestLink {'in l):
 k=int(re.search(r'weight_kind: (\d+)',line)[1]);assert k in range(5)
 ends=[]
 for which in ['producer','consumer']:
  m=re.search(which+r': CompiledPoolV1PairForestEndpoint \{ row: (\d+), slot: (\d+), pattern: (\d+) \}',line);assert m,line
  row,slot,pattern=map(int,m.groups());assert row<1024 and slot<2 and pattern<14
  ends.append(dict(endpoint=which,row=row,high_index=row>>4,low_index=row&15,slot=slot,pattern=pattern,safe=True))
 links.append(dict(index=i,weight_kind=k,endpoints=ends))
assert len(patterns)==14 and len(links)==136
owned=Path('tools/pv-b3p6-20261028/v244/host_copy_terminal_constants.rs');assert owned.read_bytes()==raw
(D/'format227-constant-guards.json').write_text(json.dumps(dict(source=str(p),sha256=hashlib.sha256(raw).hexdigest(),owned_table=str(owned),owned_bytes_equal_shipped=True,patterns=patterns,links=links,classification='exhaustive immutable constant-data bounds check; not whole-body evaluation, full structural source binding, or a theorem about a corrupted table',witness_dependent_fields_checked=False,reason='none of these fields depends on witness, claims, point, challenges, append index, or public variant'),indent=2)+'\n')
print(json.dumps(dict(patterns=len(patterns),links=len(links),safe=True)))
