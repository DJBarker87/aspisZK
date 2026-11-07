"""Prove each ACTUAL emitted call cut against its checked value continuation.
No whole-evaluator proof, global match splitting, or child unfolding.
"""
from pathlib import Path
import json
E=Path(__file__).resolve().parent
ctx={'__file__':str(E/'NMX_generate_steps.py')};exec((E/'NMX_generate_steps.py').read_text().split('manifest=[]')[0],ctx)
types=ctx['types'];plan=json.loads((E/'NMX_FOLD_PLAN.json').read_text());manifest=json.loads((E/'NMX_STEP_MANIFEST.json').read_text())
for group in range(6):
 lo=10*group+1;hi=min(10*(group+1),55);mod=f'NMX_Match{group:02d}'
 imports=['NMX_BindCongruence','NMX_PdaMap',f'NMX_Actual{group:02d}',f'NMX_Fold{group:02d}']
 if hi<55:imports.append(f'NMX_Match{group+1:02d}')
 out='\n'.join('import '+m for m in imports)+f'''\nset_option autoImplicit false
noncomputable section
namespace {mod}
open Aeneas Aeneas.Std Result AdapterRw NMX_OwnedPackets NMX_SourceModel NMX_ResultSteps
'''
 for i in range(hi,lo-1,-1):
  st=plan[i-1];kind=manifest[i-1]['kind'];params=' '.join(f'({n} : {types[n]})' for n in st['params'])
  args=' '.join(st['params']);rawargs=' '.join(n+'.payload' if n in ['master','checkpoint','lane','live'] else n for n in st['params'])
  out+=f'''\n/-- Actual emitted occurrence {i}; complete arbitrary reply/control arms. -/
theorem e{i:03d} (owners : Owners) {params} :
 NMX_Fold{group:02d}.v{i:03d} owners {args} =
 NMX_Actual{group:02d}.t{i:03d} owners {rawargs} := by
 unfold NMX_Fold{group:02d}.v{i:03d} NMX_Actual{group:02d}.t{i:03d}
'''
  if i<55:
   ns=f'NMX_Match{i//10:02d}';nextargs=' '.join(plan[i]['params']);success=f'exact {ns}.e{i+1:03d} owners {nextargs}'
   lets='\n'.join('   '+line for b in st['after'] for line in b.splitlines())
  else:success='rfl';lets=''
  if kind=='check':
   cond=st['term'][6:]
   out+=f''' by_cases condition : ({cond}) = true
 · simp only [condition,↓reduceIte]
 · simp only [condition,↓reduceIte]
'''
   if lets:out+=lets+'\n'
   out+='   '+success+'\n'
  elif kind=='snapshot':
   payload=st['term'].removeprefix('call (.snapshot ').removesuffix(')')
   out+=f' let live : Box Snapshot := ⟨owners.snapshot,{payload}⟩\n '+success+'\n'
  else:
   if kind=='pda':out+=' rw [NMX_PdaMap.try_bind]\n'
   elif kind in ['rust','box_master','box_checkpoint','box_lane']:out+=' unfold tryThen\n'
   out+=' apply NMX_BindCongruence.step\n'
   if kind in ['rust','box_master','box_checkpoint','box_lane','pda']:
    out+=' intro reply\n cases reply with\n | Err error => rfl\n | Ok '
    if kind.startswith('box_'):
     owner=kind[4:];out+=f'value =>\n   let {st["var"]} : Box {owner.capitalize()} := ⟨owners.{owner},value⟩\n'
    else:out+=(st['var'] if st['var']!='_unit' else 'unit')+' =>\n'
    if lets:out+=lets+'\n'
    out+='   '+success+'\n'
   else:
    out+=' intro '+st['var']+'\n'
    if lets:out+='\n'.join(line[2:] for line in lets.splitlines())+'\n'
    out+=' '+success+'\n'
  out+=f'#print axioms e{i:03d}\n'
 out+=f'end {mod}\nend\n';(E/(mod+'.lean')).write_text(out)
