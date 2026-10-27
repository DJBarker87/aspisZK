"""Read-only source dictionary inventory; counts are not premise discharge."""
from pathlib import Path
import hashlib,json,re
r=Path(__file__).resolve().parents[2]
b=r/'docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023'
e=r/'docs/research/100bit-spend-path-20261013/evidence/prover-dict-20261026'
s=(b/'ProverRwFullFuns.lean').read_text();ext=(b/'ProverRwFullExternalFuns.lean').read_text();types=(b/'ProverRwFullExternalTypes.lean').read_text()
ms=list(re.finditer(r'(?m)^def\s+([\w.]+)',s));d={m[1]:s[m.start():ms[i+1].start() if i+1<len(ms) else len(s)] for i,m in enumerate(ms)}
a={m[1]:int(m[2]) for m in re.finditer(r'(?m)^abbrev\s+([\w.]+)[^\n]*@ExternalFuns\.op(\d+)',ext)}
def graph(n):
 seen=set();ops=set();todo=[n]
 while todo:
  n=todo.pop()
  if n in seen:continue
  seen.add(n);t=set(re.findall(r'[\w]+(?:\.[\w]+)+',d[n]))-{n};todo+=list((t&d.keys())-seen);ops|={a[x] for x in t&a.keys()}
 return ops
body=graph('prover.prove_masked_with_attempt');outer=graph('prover.retry_attempt')
old=json.loads((e.parent/'prover-rw-20261023/native-install/dictionary-stage-b.json').read_text())['installed']
rows=[dict(id=i,name=n,in_body_overapprox=i in body,in_outer_overapprox=i in outer,inherited_source_selected=i in old) for n,i in a.items()]
ts=[dict(name=m[1],id=int(m[2]),status='OPEN: exact retained extraction or wrapper contract and carrier transport required; no representation is invented') for m in re.finditer(r'(?m)^abbrev\s+([\w.]+)[^\n]*@ExternalTypes\.op(\d+)',types)]
x=dict(base_revision='da25b1e8b3',source_hashes={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in b.glob('ProverRwFull*.lean')},functions=rows,types=ts,root_premises_removed=0,qualification='Syntactic reachability overapproximates success: errors inside proof body are included. File/ROM/entropy/reservation effects belong to sibling; generic error combinators are installed separately. All native associations require actual extraction or existing named trust, not arbitrary type instantiation.')
(e/'inventory.json').write_text(json.dumps(x,indent=2)+'\n')
print(len(rows),len(ts))
