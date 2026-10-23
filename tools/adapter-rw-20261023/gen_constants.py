"""Prove a small arithmetic DAG from emitted initializers; no native evaluation.
Every operation is replaced by a named, generic scalar theorem.
"""
from pathlib import Path
import re,sys
R=Path(__file__).resolve().parents[2];L=R/'docs/research/100bit-spend-path-20261013/lean'
s=(L/'AdapterRwModel.lean').read_text();defs={}
ms=list(re.finditer(r'(?m)^(?:def|impl_def)\s+([\w.]+)',s))
for i,m in enumerate(ms):
 chunk=s[m.end():ms[i+1].start() if i+1<len(ms) else len(s)]
 if ':=' not in chunk:continue
 sig,body=chunk.split(':=',1);body=body.split('/--')[0].strip();defs[m[1]]=(sig,body)
values={};lemmas=[]
def go(name):
 if name in values:return values[name]
 sig,body=defs[name];ops='(ops : Ops)' in sig;env={};steps=[];used=[]
 def expression(expr):
  expr=' '.join(expr.split())
  match=re.fullmatch(r'(.+?) ([+*\-]) (.+)',expr)
  if match:
   a,op,b=match.groups();x=expression(a);y=expression(b);z={'+':lambda:x+y,'*':lambda:x*y,'-':lambda:x-y}[op]()
   assert 0<=z<2**32
   lemma={'+':'add_eq','*':'mul_eq','-':'sub_eq'}[op]
   args=f'{x}#usize {y}#usize {z}#usize '+('(by scalar_tac) ' if op=='-' else '')+'(by scalar_tac)'
   steps.append(f'  rw [Scalar.{lemma} {args}]\n  all_goals try simp only [bind_tc_ok]')
   return z
  if re.fullmatch(r'\d+#usize',expr):return int(expr.split('#')[0])
  if expr in env:return env[expr]
  ref=expr.removeprefix('(').removesuffix(')').replace(' ops','');value=go(ref)
  used.append('constant_'+ref.replace('.','_')+(' ops' if '(ops : Ops)' in defs[ref][0] else ''))
  return value
 body=re.sub(r'^do\s*','',body)
 parts=re.split(r'\blet\s+(\w+)\s*←\s*',body)
 if len(parts)>1:
  for i in range(1,len(parts),2):
   var=parts[i];rest=parts[i+1]
   if i+2==len(parts):
    # final let binding and final return occupy separate logical lines.
    lines=rest.strip().splitlines();rhs=lines[0].strip();last=' '.join(x.strip() for x in lines[1:])
    env[var]=expression(rhs)
    value=expression(last)
   else:env[var]=expression(rest.strip())
 else:value=expression(body)
 label='constant_'+name.replace('.','_');parameter=' (ops : AdapterRw.Ops)' if ops else ''
 term='AdapterRw.'+name+(' ops' if ops else '')
 pure='Result' not in sig
 goal=f'{value}#usize' if pure else f'ok {value}#usize'
 proof=[f'theorem {label}{parameter} : {term} = {goal} := by',f'  unfold AdapterRw.{name}']
 if used:proof.append('  rw ['+', '.join(dict.fromkeys(used))+']')
 if used:proof.append('  all_goals try simp only [bind_tc_ok]')
 proof+=steps
 proof.append('  all_goals rfl')
 lemmas.append('\n'.join(proof));values[name]=value
 return value
roots=['aspis_r1_cost_probe.verifier.PROOF_BYTES','aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES']
for name in roots:print(name,go(name))
out='import AdapterRwScalar\nset_option autoImplicit false\nnamespace AspisR1.AdapterRw.Constants\nopen Aeneas Aeneas.Std Result\n\n'+'\n\n'.join(lemmas)+'\n\n'
for name in values:out+='#print axioms constant_'+name.replace('.','_')+'\n'
out+='end AspisR1.AdapterRw.Constants\n'
p=L/'AdapterRwConstants.lean'
if '--check' in sys.argv:assert p.read_text()==out
else:p.write_text(out)
