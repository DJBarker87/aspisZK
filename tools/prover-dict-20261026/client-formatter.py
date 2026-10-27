"""Generate only new caller erasure statements using already checked helper equations."""
from pathlib import Path
import re,json
r=Path(__file__).resolve().parents[2];p=r/'docs/research/v8-r0-zk-20261009/lean/R1Z';s=(r/'docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean').read_text();ms=list(re.finditer(r'(?m)^def\s+([\w.]+)',s));d={m[1]:s[m.end():ms[i+1].start() if i+1<len(ms) else len(s)] for i,m in enumerate(ms)};known={}
for f in [*p.glob('PDict_FmtErase*.lean'),p/'PDict_FmtRetryComplete.lean',p/'PDict_FmtSemantics.lean',p/'PDict_FmtMaskedBody.lean',p/'PDict_FmtPublicationFrame.lean']:
 for t,n in re.findall(r'theorem (erase_\d+).*?@([\w.]+) _ \(replace ops other\)',f.read_text(),re.S):known[n]=t
ext=(r/'docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullExternalFuns.lean').read_text();aliases={m[1]:int(m[2]) for m in re.finditer(r'(?m)^abbrev\s+([\w.]+)[^\n]*@ExternalFuns\.op(\d+)',ext)}
refs={n:set(re.findall(r'\b\w+(?:\.\w+)+',t)) for n,t in d.items()};deps={n:(refs[n]&d.keys())-{n} for n in d};closed={};order=[]
def closure(n):
 if n in closed:return closed[n]
 closed[n]={aliases[a] for a in refs[n]&aliases.keys()}
 for c in sorted(deps[n]):closed[n]|=closure(c)
 return closed[n]
def visit(n):
 if n in known or n in order:return
 for c in sorted(deps[n]):visit(c)
 order.append(n)
visit('RealR1_client.prove_for_proof_accounts');use=[n for n in order if closure(n)];assert all(85 not in closure(n) for n in use);new={n:'client_'+str(i) for i,n in enumerate(use)};names=known|new
prior='PDict_FormatterIndependent'
for k,start in enumerate(range(0,len(use),4)):
 name='PDict_FmtClient'+str(k);out=f'''import R1Z.{prior}
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_FmtErase
open Aeneas Aeneas.Std ProverRwFull
variable [ExternalTypes]
'''
 for n in use[start:start+4]:
  cs=[names[c]+' ops other' for c in sorted(deps[n]) if c in names]
  out+=f'\n/-- Formatter irrelevance for the complete emitted `{n}`. -/\ntheorem {new[n]} (ops other : ExternalFuns) :\n    @{n} _ (replace ops other) = @{n} _ ops := by\n  delta {n}\n'
  if cs:out+='  try simp only ['+', '.join(cs)+']\n'
  out+=f'  all_goals rfl\n#print axioms {new[n]}\n'
 out+='end R1Z.PDict_FmtErase\n';(p/(name+'.lean')).write_text(out);prior=name
print([(new[n],n) for n in use])
