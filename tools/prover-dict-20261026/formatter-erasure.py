"""Generate symbolic, dependency-by-dependency formatter erasure statements.
Does not modify extracted sources, compile, launch, or claim native association.
"""
from pathlib import Path
import re,json
r=Path(__file__).resolve().parents[2];p=r/'docs/research/v8-r0-zk-20261009/lean/R1Z';e=r/'docs/research/100bit-spend-path-20261013/evidence/prover-dict-20261026/continued'
s=(r/'docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean').read_text()
# Strip nested comments and string literals before identifying source references.
out=[];i=0;depth=0;quoted=False
while i<len(s):
 pair=s[i:i+2];c=s[i]
 if not quoted and pair=='/-':depth+=1;i+=2;continue
 if depth and pair=='-/':depth-=1;i+=2;continue
 if depth:
  if c=='\n':out.append(c)
  i+=1;continue
 if not quoted and pair=='--':
  end=s.find('\n',i);i=len(s) if end<0 else end;continue
 if c=='"' and (i==0 or s[i-1]!='\\'):quoted=not quoted;out.append(' ');i+=1;continue
 out.append(' ' if quoted else c);i+=1
s=''.join(out)
ms=list(re.finditer(r'(?m)^def\s+([\w.]+)',s));d={m[1]:s[m.end():ms[i+1].start() if i+1<len(ms) else len(s)] for i,m in enumerate(ms)}
ext=(r/'docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullExternalFuns.lean').read_text();a={m[1]:int(m[2]) for m in re.finditer(r'(?m)^abbrev\s+([\w.]+)[^\n]*@ExternalFuns\.op(\d+)',ext)}
deps={n:(set(re.findall(r'\b[\w]+(?:\.[\w]+)+',t))&d.keys())-{n} for n,t in d.items()}
direct={n:{a[x] for x in set(re.findall(r'\b[\w]+(?:\.[\w]+)+',t))&a.keys()} for n,t in d.items()}
closure={};ordered=[]
def visit(n):
 if n in closure:return
 closure[n]=set(direct[n])
 for child in sorted(deps[n]):
  assert child!=n,('recursive body',n)
  visit(child);closure[n]|=closure[child]
 ordered.append(n)
visit('prover.retry_attempt')
use=[n for n in ordered if closure[n]]
assert all(85 not in closure[n] for n in use)
idx={n:i for i,n in enumerate(use)}
(e/'formatter-erasure-plan.json').write_text(json.dumps(dict(root='prover.retry_attempt',source_functions=len(ordered),external_dependent=len(use),reachable_operations=sorted(closure['prover.retry_attempt']),formatter_used=False,functions=[dict(name=n,theorem='erase_'+str(idx[n]),dependencies=sorted(deps[n]),external_ops=sorted(closure[n])) for n in use]),indent=2)+'\n')
print('functions',len(ordered),'external dependent',len(use))
# Small batches keep the symbolic checks focused and avoid deep unfolding.
size=16
for chunk,start in enumerate(range(0,len(use),size)):
 module=f'PDict_FmtErase{chunk:02d}'
 prior='PDict_FmtEraseBase' if chunk==0 else f'PDict_FmtErase{chunk-1:02d}'
 text=f'''import R1Z.{prior}
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_FmtErase
open Aeneas Aeneas.Std ProverRwFull
variable [ExternalTypes]
'''
 for n in use[start:start+size]:
  children=[f'erase_{idx[c]}' for c in sorted(deps[n]) if c in idx]
  text+=f'\n/-- Full symbolic source-function equality for `{n}`. -/\ntheorem erase_{idx[n]} (ops other : ExternalFuns) :\n    @{n} _ (replace ops other) = @{n} _ ops := by\n  delta {n}\n'
  if children:text+='  try simp only ['+', '.join(children)+']\n'
  text+='  all_goals rfl\n'
  text+=f'#print axioms erase_{idx[n]}\n'
 text+='end R1Z.PDict_FmtErase\n'
 if chunk>=3:
  text=re.sub(r'  try simp only \[(.*?)\]\n  all_goals rfl',r'  first | rfl | (try simp only [\1]; all_goals rfl)',text)
 if chunk>2 or not (p/(module+'.lean')).exists():
  (p/(module+'.lean')).write_text(text)
base='''import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_FmtErase
open Aeneas Aeneas.Std ProverRwFull
variable [ExternalTypes]
@[reducible] def replace (ops other : ExternalFuns) : ExternalFuns :=
  { ops with op85 := other.op85 }
end R1Z.PDict_FmtErase
'''
(p/'PDict_FmtEraseBase.lean').write_text(base)
