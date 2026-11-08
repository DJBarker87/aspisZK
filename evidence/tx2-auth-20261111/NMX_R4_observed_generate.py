from pathlib import Path
import json,re
E=Path(__file__).resolve().parent
ctx={'__file__':str(E/'NMX_generate_steps.py')};exec((E/'NMX_generate_steps.py').read_text().split('manifest=[]')[0],ctx)
types=ctx['types'];plan=json.loads((E/'NMX_FOLD_PLAN.json').read_text());manifest=json.loads((E/'NMX_STEP_MANIFEST.json').read_text())
for group in range(6):
 lo=10*group+1;hi=min(10*(group+1),55);mod=f'NMX_R4_Observed{group:02d}'
 imports=['NMX_R4_CallContext','NMX_R4_PdaObservation',f'NMX_R4_CallScript{group:02d}',f'NMX_Fold{group:02d}']
 if group<5:imports.insert(0,'NMX_R4_FreeCongruence')
 if hi<55:imports.append(f'NMX_R4_Observed{group+1:02d}')
 out='\n'.join('import '+m for m in imports)+f'''\nset_option autoImplicit false
noncomputable section
namespace {mod}
open Aeneas Aeneas.Std Result AdapterRw NMX_OwnedPackets NMX_SourceModel NMX_R4_CallRun NMX_R4_CallContext
'''
 for i in range(hi,lo-1,-1):
  st=plan[i-1];kind=manifest[i-1]['kind'];names=[n for n in st['params'] if n!='ops']
  params=' '.join(f'({n} : {types[n]})' for n in names)
  args=' '.join('(ops c)' if n=='ops' else n for n in st['params'])
  out+=f'''\ntheorem e{i:03d} (c : Context) {params} :
 observe c (NMX_R4_CallScript{group:02d}.t{i:03d} c.owners {args}) =
 NMX_R2_NativeExecution.run c.owners c.allocations c.failure c.lane c.registry c.env
  (NMX_Fold{group:02d}.p{i:03d} c.owners {args}) := by
 unfold NMX_R4_CallScript{group:02d}.t{i:03d} NMX_Fold{group:02d}.p{i:03d}
'''
  success='rfl' if i==55 else f'exact NMX_R4_Observed{i//10:02d}.e{i+1:03d} c '+ ' '.join(n for n in plan[i]['params'] if n!='ops')
  if kind=='check':
   cond=st['term'][6:];out+=f' cases condition : ({cond}) with\n | true => rfl\n | false => {success}\n'
  else:
   helper='child' if kind in ['rust','box_master','box_checkpoint','box_lane'] else 'snapshot' if kind=='snapshot' else 'step' if kind=='pda' else 'scalar'
   if helper in ['child','step']:
    nextargs=' '.join('(ops c)' if n=='ops' else n for n in plan[i]['params'])
    actual=f'NMX_R4_CallScript{i//10:02d}.t{i+1:03d} c.owners '+nextargs
    source=f'NMX_Fold{i//10:02d}.p{i+1:03d} c.owners '+nextargs
    premise='NMX_R4_Observed'+str(i//10).zfill(2)+f'.e{i+1:03d} c '+ ' '.join(n for n in plan[i]['params'] if n!='ops')
    out=out.replace(f' unfold NMX_R4_CallScript{group:02d}.t{i:03d} NMX_Fold{group:02d}.p{i:03d}\n',f' unfold NMX_Fold{group:02d}.p{i:03d}\n')
    if helper=='child':
     command=st['term'][5:]
     theorem=f'NMX_R4_ObservedStep.child c {command}'
     ideal=f'NMX_R4_CallProgram.bind (NMX_R4_CallProgram.child {command}) (fun reply => NMX_R4_TryObservation.after reply (fun {st["var"]} => {actual}))'
    else:
     raw=(E/f'NMX_R4_CallScript{group:02d}.lean').read_text().split(f'def t{i:03d}',1)[1].split('\ndef ',1)[0]
     inst=re.search(r'core.result.Result.map_err\s+([A-Za-z_0-9.]+)',raw)[1]
     args=st['term'][len('call (.pda '):-1]
     theorem=f'NMX_R4_PdaObservation.step c {args} {inst} (by rfl)'
     ideal=f'NMX_R4_CallProgram.bind (NMX_R4_CallProgram.pda {args}) (fun reply => NMX_R4_PdaObservation.after {inst} reply (fun {st["var"]} => {actual}))'
    out+=f' have same : NMX_R4_CallScript{group:02d}.t{i:03d} c.owners {args if False else " ".join("(ops c)" if n=="ops" else n for n in st["params"])} = {ideal} := by\n'
    out+=f'  unfold NMX_R4_CallScript{group:02d}.t{i:03d} '+('NMX_R4_PdaObservation.after ' if helper=='step' else '')+'NMX_R4_TryObservation.after\n'
    out+='  apply NMX_R4_FreeCongruence.step\n  intro reply\n  apply NMX_R4_FreeCongruence.step\n  intro response\n'
    if helper=='step':out+='  apply NMX_R4_FreeCongruence.step\n  intro control\n  cases control <;> rfl\n'
    else:out+='  cases response <;> rfl\n'
    out+=' rw [same]\n'
    out+=f' have h := {theorem} (fun {st["var"]} => {actual}) (fun {st["var"]} => {source}) (fun {st["var"]} => {premise})\n'
    out+=' exact h\n'
    out+=f'#print axioms e{i:03d}\n'
    continue
   out+=' apply NMX_R4_ObservedStep.'+helper+'\n'
   out+=' intro '+st['var']+'\n'
   if st['after'] and i<55:
    out+=' simp only [NMX_R4_CallLaws.observed_scalar,NMX_R3_RegistryRun.scalar,NMX_R2_Observation.bind]\n'
    out+='\n'.join(' '+line for b in st['after'] for line in b.splitlines())+'\n'
   out+=' '+success+'\n'
  out+=f'#print axioms e{i:03d}\n'
 out+=f'end {mod}\nend\n';(E/(mod+'.lean')).write_text(out)
