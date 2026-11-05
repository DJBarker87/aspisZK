"""Compare the exact non-control reader-entry source after its control repair."""
from pathlib import Path
import hashlib,json,re
E=Path(__file__).resolve().parent

def erase(s):
 needle='if cfg!(NID_invert)'
 while needle in s:
  a=s.index(needle);b=s.index('{',a);depth=1;c=b+1
  while depth:
   depth += (s[c]=='{')-(s[c]=='}');c+=1
  s=s[:a]+s[c:]
 return re.sub(r'\s+','',re.sub(r'\blet\s+mut\s+','let ',s))
paths=[E/a/'sources/NID_src/crates/aspis-r1-cost-probe/src/NID_native.rs' for a in ['NID_K003','NID_K004']]
a,b=[p.read_text() for p in paths]
assert erase(a)==erase(b),'non-control source changed'
assert erase(b)!=erase(b.replace('log.base==bytes.as_ptr() as usize','log.base!=bytes.as_ptr() as usize')),'predicate mutation control'
assert erase(b)!=erase(b.replace('&mut self','&self')),'receiver mutation control'
out=dict(status='PASS',paths=[str(p.relative_to(E)) for p in paths],non_control_token_sha256=hashlib.sha256(erase(a).encode()).hexdigest(),erasure='Remove disabled NID_invert branches and mutable-local binding qualifiers only; native predicates/calls/assignments otherwise exact',mutation_detected=True)
(E/'NID_CONTROL_ERASURE.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
