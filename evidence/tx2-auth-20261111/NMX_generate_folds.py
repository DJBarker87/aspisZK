"""Fold checked single-occurrence equations, retaining every continuation.
Generated suffixes are value/owner support only, never candidate roots.
"""
from pathlib import Path
import re,json
E=Path(__file__).resolve().parent
# Reuse the generator's type table without replacing its outputs.
ctx={'__file__':str(E/'NMX_generate_steps.py')};exec((E/'NMX_generate_steps.py').read_text().split('manifest=[]')[0],ctx)
blocks=ctx['blocks'];types=ctx['types'];manifest=json.loads((E/'NMX_STEP_MANIFEST.json').read_text())
steps=[];pending=[]
for b in blocks:
 m=re.match(r'let (\w+) ← (.*)',b,re.S)
 if m or b.startswith(('call ','check ')):
  if steps:steps[-1]['after']=pending
  pending=[];i=len(steps)+1
  steps.append(dict(n=i,var=m[1] if m else '_unit',term=m[2] if m else b,A=types[m[1]] if m else 'Unit'))
 else:pending.append(b)
steps[-1]['after']=pending
# Liveness from all variables in each remaining source suffix, excluding future binders.
prev=['ops','verifier','accounts','pool','outputLane','slot']
for i,st in enumerate(steps):
 rest='\n'.join(blocks[blocks.index(next(b for b in blocks if b.endswith(st['term']) or b==st['term'])):]) if False else ''
 # Full context is simpler and makes argument provenance explicit.
 st['params']=list(prev)
 if st['var']!='_unit':prev.append(st['var'])
 for b in st.get('after',[]):
  m=re.match(r'let (\w+) := ',b)
  if m:prev.append(m[1])
# Strip unused parameters using backward dependency analysis.
needed=set()
for st in reversed(steps):
 text=st['term']+'\n'+'\n'.join(st['after'])
 local={st['var']}
 local.update(re.findall(r'let (\w+) := ', '\n'.join(st['after'])))
 needed=(needed-local)|{n for n in types if re.search(r'(?<![\w.])'+n+r'\b',text)}
 st['params']=['ops']+[n for n in st['params'] if n in needed and n!='ops']
for st in steps:
 for n in st['params']:assert n in types,n
# The final returned value is an owned Auth; normal allocation semantics only.
for group in range(6):
 lo=group*10+1;hi=min((group+1)*10,55)
 if lo>hi:continue
 # Files compile from tail group to head, while per-call statements compile source-order.
 imports=['NMX_S%03d'%i for i in range(lo,hi+1)]
 if group in [1,2,4]:imports+=['NMX_UnusedWitnesses']
 if hi<55:imports+=['NMX_Fold%02d'%(group+1)]
 out='\n'.join('import '+m for m in imports)+f'''\nset_option autoImplicit false
noncomputable section
namespace NMX_Fold{group:02d}
open Aeneas Aeneas.Std Result AdapterRw NMX_OwnedPackets NMX_Program NMX_SourceModel NMX_ResultSteps
'''
 for st in reversed(steps[lo-1:hi]):
  i=st['n'];params=' '.join(f'({n} : {types[n]})' for n in st['params'])
  after='\n'.join(st['after'])
  if i==55:
   assert after.startswith('pure ');payload=after[5:];contP='.ret '+payload;contR='ok (.Ok (('+payload+' : Auth).erase))'
  else:
   nxt=steps[i];ns=f'NMX_Fold{(i)//10:02d}'
   args=' '.join(nxt['params'])
   contP=f'{ns}.p{i+1:03d} owners {args}'
   contR=f'{ns}.v{i+1:03d} owners {args}'
   for b in reversed(st['after']):
    assert b.startswith('let '),b
    contP=b+'\n'+contP;contR=b+'\n'+contR
  contP='fun '+st['var']+' =>\n  '+contP.replace('\n','\n  ')
  contR='fun '+('value' if st['var']=='_unit' else st['var'])+' =>\n  '+contR.replace('\n','\n  ')
  # Extract the checked RHS and replace exactly its erased continuation.
  sr=(E/f'NMX_S{i:03d}.lean').read_text();rhs=sr.split(' next) ()) =\n',1)[1].split(' := by',1)[0]
  rhs=rhs.replace('NMX_ValueLink.erase (eval (source ops owners) (next value) ())','NEXT value')
  rhs=rhs.replace('NMX_ValueLink.erase (eval (source ops owners) (next ()) ())','NEXT ()')
  rhs=rhs.replace('NMX_ValueLink.erase (eval (source ops owners) (next ⟨owners.master,value⟩) ())','NEXT ⟨owners.master,value⟩')
  rhs=rhs.replace('NMX_ValueLink.erase (eval (source ops owners) (next ⟨owners.checkpoint,value⟩) ())','NEXT ⟨owners.checkpoint,value⟩')
  rhs=rhs.replace('NMX_ValueLink.erase (eval (source ops owners) (next ⟨owners.lane,value⟩) ())','NEXT ⟨owners.lane,value⟩')
  # Snapshot expression has no generic value binder.
  rhs=re.sub(r'NMX_ValueLink.erase \(eval \(source ops owners\) \(next (⟨owners.snapshot,.*⟩)\) \(\)\)',r'NEXT \1',rhs,flags=re.S)
  assert 'NMX_ValueLink.erase' not in rhs,(i,rhs)
  rhs=rhs.replace('NEXT', '('+contR+')')
  out+=f'''\ndef p{i:03d} (owners : Owners) {params} : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.{st['term']}) ({contP})
def v{i:03d} (owners : Owners) {params} : Final :=
 {rhs}
theorem e{i:03d} (owners : Owners) {params} :
 NMX_ValueLink.erase (eval (source ops owners) (p{i:03d} owners {' '.join(st['params'])}) ()) =
 v{i:03d} owners {' '.join(st['params'])} := by
 unfold p{i:03d} v{i:03d}
 rw [NMX_S{i:03d}.step ops owners {' '.join(n if n in st['params'] else 'NMX_UnusedWitnesses.'+n for n in manifest[i-1]['parameters'])}]
'''
  if i==55:out+=' rfl\n'
  else:out+=f' simp only [{ns}.e{i+1:03d}] <;> rfl\n'
  out+=f'#print axioms e{i:03d}\n'
 out+=f'end NMX_Fold{group:02d}\nend\n'
 if group!=5: (E/f'NMX_Fold{group:02d}.lean').write_text(out)
 # Fold05 already accepted at L128; its proof text remains frozen.
(E/'NMX_FOLD_PLAN.json').write_text(json.dumps(steps,indent=1)+'\n')
