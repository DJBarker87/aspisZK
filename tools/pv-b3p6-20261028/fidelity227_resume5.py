"""Per-function D188 syntax inventory. This scan cannot grant fidelity credit.
Every mutable restoration must be both present and subsequently applied. Concrete
native/emission comparisons for changed writes are tracked separately.
"""
from pathlib import Path
import re,json,hashlib
D=Path('evidence/pv-b3p6-20261028');p=D/'raw227-complete-resume5/Funs.lean';s=p.read_text();rows=[]
for b in re.split(r'(?=^/-- \[)',s,flags=re.M):
 m=re.search(r'^def\s+(\S+)',b,re.M)
 if not m:continue
 restores=[]
 for a in re.finditer(r'let \(([^\n]*)\) ← Array\.index_mut_usize ([^\n]*)',b):
  fields=[q.strip()for q in a[1].split(',')];assert len(fields)==2
  back=fields[-1];uses=len(re.findall(r'\b'+re.escape(back)+r'\b',b))
  restores.append(dict(binding=a[0],restoration=back,uses=uses,applied=back!='_' and uses>=2))
 assert all(r['applied']for r in restores),(m[1],restores)
 assert not re.search(r'iter_mut|next_back|chunks_mut',b),m[1]
 underscores=[line.strip()for line in b.splitlines()if re.search(r'\b_\b',line)]
 rows.append(dict(function=m[1],mutable_restorations=restores,direct_array_updates=len(re.findall(r'Array\.update\b',b)),discard_bindings=underscores,concrete_native_emission_comparison='pending' if restores or 'Array.update'in b else 'not required by mutable-write scan',fidelity_credit=False))
assert len(rows)==191
out=dict(raw_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),definitions=191,restorations=sum(len(r['mutable_restorations'])for r in rows),dropped_restorations=0,scope='syntactic scan only; does not establish backward-state flow/value equality or close D188 for mutable functions',rows=rows)
(D/'fidelity227-resume5.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items()if k!='rows'}))
