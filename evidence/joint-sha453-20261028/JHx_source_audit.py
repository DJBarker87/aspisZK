"""Check bounded computation shape and every delivered top-level axioms print."""
from pathlib import Path
import re,json,collections
E=Path(__file__).resolve().parent;R=E.parents[1];L=R/'lean';x=json.loads((E/'JHx_GENERATOR_CHECK.json').read_text());r=[]
computations={m['module'] for m in x['computations']}
for p in sorted(L.glob('JHx_*.lean')):
 s=p.read_text();theorems=re.findall(r'^(?:theorem|instance) (\w+)',s,re.M);audits=re.findall(r'^#print axioms (\w+)',s,re.M)
 assert collections.Counter(theorems)==collections.Counter(audits),(p,theorems,audits)
 assert not re.search(r'\b(sorry|axiom|native_decide|norm_num|simp_all)\b',s),p
 if p.stem not in computations:assert 'unfold compress' not in s and 'unfold JFp_SHA256.hash' not in s
 else:
  assert s.count('  unfold compress loop')==sum(1 for q in s.splitlines() if q.startswith('theorem checked'))
  assert s.count('  have t')==64*s.count('  unfold compress loop')
 r.append(dict(module=p.stem,theorems=len(theorems),axioms_prints=len(audits),whole_hash_or_compression_reflexivity=False))
(E/'JHx_SOURCE_AUDIT.json').write_text(json.dumps(dict(passed=True,results=r),indent=2)+'\n');print('source audit passed',len(r),'modules')
