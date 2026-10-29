"""Keep the selector frame explicit when joining the previous fifteen-stage plan."""
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
s='import PV_B3P_ValueCpsBridge10227\n'+header
s+='\nattribute [local irreducible] aspis_core.field.QM31.add aspis_core.field.QM31.sub aspis_core.field.QM31.square aspis_core.field.QM31.mul aspis_core.field.QM31.mul_m31 Array.index_usize Array.update reference_terminal.read227 reference_terminal.reconstruct_10 reference_terminal.add_preweighted reference_copy_terminal.Selectors.row\n'
for i in range(1,14):
 s+=f'''\ntheorem value_selector_frame10_{i:02} {{β : Type}} {params}
    (selector : aspis_core.field.QM31) (range_input : Array aspis_core.field.QM31 33#usize)
    (f : ValueState9 → Result β) :
    (value_owned_stage9_{i:02} packed openings selectors (selector,range_input) >>= f) =
    (value_owned_stage9_{i:02} packed openings selectors (selector,range_input) >>= (fun next => f (selector,next.2))) := by
  unfold value_owned_stage9_{i:02} value_read_context9_{i:02}
  simp only [PV_B3P_Ordered227.bind_assoc,bind_tc_ok]
#print axioms value_selector_frame10_{i:02}
'''
s+='end PV_B3P_Binding10227\n';p=L/'PV_B3P_ValueFrames10227.lean'
if '--check'in sys.argv:assert p.read_text()==s
else:p.write_text(s)
s='import PV_B3P_ValueFrames10227\n'+header
s+='\nattribute [local irreducible] '+' '.join(f'value_owned_stage9_{i:02}'for i in range(15))+' value_selector10 '+' '.join(f'value_owned_cont10_{i:02}'for i in range(1,15))+'\n'
s+=f'''\ntheorem value_sequence_cps10 {params} :
    value_owned_sequence9 packed openings selectors = value_owned_cps10 packed openings selectors := by
  unfold value_owned_sequence9 value_owned_cps10
  rw [value_selector_pair10]
  simp only [PV_B3P_Ordered227.bind_assoc,bind_tc_ok]
  apply bind_equal9
  intro selector
'''
for i in range(1,14):
 inp='(Array.repeat 33#usize aspis_core.field.QM31.ZERO)'if i==1 else f's{i-1}.2'
 s+=f'  rw [value_selector_frame10_{i:02} packed openings selectors selector {inp}]\n  conv_rhs => unfold value_owned_cont10_{i:02}\n  apply bind_equal9\n  intro s{i}\n'
s+='  unfold value_owned_cont10_14\n  rfl\n'
s+=f'''\ntheorem value_entry_factor10 {params} :
    reference_terminal.add_value_lanes packed openings selectors = value_owned_sequence9 packed openings selectors :=
  (value_entry_cps10 packed openings selectors).trans (value_sequence_cps10 packed openings selectors).symm

theorem add_value_read_binding10 {params} :
    reference_terminal.add_value_lanes packed openings selectors = value_direct_sequence9 packed openings selectors :=
  (value_entry_factor10 packed openings selectors).trans (value_sequence_read_binding9 packed openings selectors)
#print axioms value_sequence_cps10
#print axioms value_entry_factor10
#print axioms add_value_read_binding10
end PV_B3P_Binding10227
''';p=L/'PV_B3P_ValueSequenceBridge10227.lean'
if '--check'in sys.argv:assert p.read_text()==s
else:p.write_text(s)
