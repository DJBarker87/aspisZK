"""Compose only named stage equations, with all stage bodies irreducible."""
from pathlib import Path
import json,sys
D=Path('evidence/pv-b3p6-20261028');L=D/'lean';O=D/'resume10'
params='''(packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors)'''
header='''namespace PV_B3P_Binding10227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227
set_option autoImplicit false
'''
files={}
for i in reversed(range(15)):
 m=f'PV_B3P_ValueCompose10{i:02}227';tail=f'value_owned_tail10_{i:02}';direct=f'value_direct_tail10_{i:02}';nxt=f'value_owned_tail10_{i+1:02}';nxtd=f'value_direct_tail10_{i+1:02}'
 src='reference_terminal.add_value_lanes'if i==0 else f'value_source_tail10_{i:02}';args='packed openings selectors'+(' state'if i else'');pp=params+(' (state : ValueState9)'if i else'')
 imp='PV_B3P_ValueEntry10227'if i==0 else f'PV_B3P_ValueTail10{i:02}227'
 s=f'import {imp}\n'+(f'import PV_B3P_ValueCompose10{i+1:02}227\n'if i<14 else'')+header
 for kind,fn,nextfn in [('owned',tail,nxt),('direct',direct,nxtd)]:
  s+=f'\ndef {fn} {pp} : Result (Array aspis_core.field.QM31 24#usize) :=\n  value_{kind}_stage9_{i:02} {args}'+(f' >>= {nextfn} packed openings selectors'if i<14 else'')+'\n'
 s+='\nattribute [local irreducible] '+ ' '.join(f'value_{kind}_stage9_{j:02}'for kind in ['owned','direct']for j in range(i,15))+'\n'
 s+=f'\ntheorem value_tail_factor10_{i:02} {pp} :\n    {src} packed openings selectors{(' state.1 state.2'if i else'')} = {tail} {args} := by\n  rw [value_source_equation10_{i:02}]\n'
 if i<14:
  s+=f'  change (value_owned_stage9_{i:02} {args} >>= (fun next => value_source_tail10_{i+1:02} packed openings selectors next.1 next.2)) = _\n'
  s+=f'  apply congrArg (fun next => value_owned_stage9_{i:02} {args} >>= next)\n  funext next\n  exact value_tail_factor10_{i+1:02} packed openings selectors next\n'
 else:s+='  rfl\n'
 s+=f'\ntheorem value_tail_read_binding10_{i:02} {pp} :\n    {tail} {args} = {direct} {args} := by\n  unfold {tail} {direct}\n  rw [value_stage_read_binding9_{i:02}]\n'
 if i<14:
  s+=f'  apply congrArg (fun next => value_direct_stage9_{i:02} {args} >>= next)\n  funext next\n  exact value_tail_read_binding10_{i+1:02} packed openings selectors next\n'
 s+=f'\n#print axioms value_tail_factor10_{i:02}\n#print axioms value_tail_read_binding10_{i:02}\nend PV_B3P_Binding10227\n';files[m]=s
s='import PV_B3P_ValueCompose1000227\nimport PV_B3P_ValueReadSequence9227\n'+header
s+='\nattribute [local irreducible] '+' '.join(f'value_{kind}_stage9_{i:02}'for kind in ['owned','direct']for i in range(15))+'\n'
s+=f'''\ntheorem value_entry_factor10 {params} :
    reference_terminal.add_value_lanes packed openings selectors =
      value_owned_sequence9 packed openings selectors := by
  rw [value_tail_factor10_00]
  simp only [value_owned_sequence9, '''+', '.join(f'value_owned_tail10_{i:02}'for i in range(15))+''']
'''
s+=f'''\ntheorem add_value_read_binding10 {params} :
    reference_terminal.add_value_lanes packed openings selectors =
      value_direct_sequence9 packed openings selectors :=
  (value_entry_factor10 packed openings selectors).trans
    (value_sequence_read_binding9 packed openings selectors)
#print axioms value_entry_factor10
#print axioms add_value_read_binding10
end PV_B3P_Binding10227
''';files['PV_B3P_ValueReadBridge10227']=s
for m,s in files.items():
 p=L/(m+'.lean')
 if '--check'in sys.argv:assert p.read_text()==s,m
 else:p.write_text(s)
p=O/'value-composition.json';record=dict(modules=list(files),credit='actual emitted entry factorization and read binding; other source transformations remain open',shape='one named factor and one named read law per stage; opaque stage bodies; root composes equations only')
if '--check'in sys.argv:assert json.loads(p.read_text())==record
else:p.write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record))
