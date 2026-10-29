"""Apply the bounded usize loop law to the three actual ten-cell source loops."""
from pathlib import Path
import json,sys
D=Path('evidence/pv-b3p6-20261028');L=D/'lean';O=D/'resume10';files={}
header='''namespace PV_B3P_Binding10227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227
set_option autoImplicit false
'''
s='import PV_B3P_DigitRead10227\nimport PV_B3P_NineUnroll9227\n'+header
s+='''
theorem next_zero10 : Usize.wrapping_add 0#usize 1#usize = 1#usize := next_exact _ _ rfl
#print axioms next_zero10

theorem digit_loop_ten10 (values : Array aspis_core.field.QM31 16#usize)
    (offset : Option Usize) (range : DigitRange10) :
    loop (usize_body (digit_source_step10 values offset) 10#usize) (range,0#usize) =
      PV_B3P_Ordered227.fold (digit_source_step10 values offset)
        [0#usize,1#usize,2#usize,3#usize,4#usize,5#usize,6#usize,7#usize,8#usize,9#usize] range := by
  rw [usize_loop_plan (digit_source_step10 values offset) 10#usize 0#usize 10 range rfl]
  simp only [usize_plan,next_zero10,next_1,next_2,next_3,next_4,next_5,next_6,next_7,next_8,next_9,PV_B3P_Ordered227.fold]
#print axioms digit_loop_ten10
end PV_B3P_Binding10227
''';files['PV_B3P_DigitLoop10227']=s
for region in range(3):
 i=region*2+1;j=i+1;field=['z','succ_z','xor12_z'][region];offset=['none','(some 10#usize)','(some 20#usize)'][region]
 s=f'import PV_B3P_DigitLoop10227\nimport PV_B3P_DigitStage10{i:02}227\nimport PV_B3P_DigitStage10{j:02}227\n'+header
 s+='\nattribute [local irreducible] digit_source_step10 value_direct_stage9_'+f'{i:02} value_direct_stage9_{j:02}\n'
 s+=f'''\ntheorem digit_pair_loop_binding10_{region}
    (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (selector : aspis_core.field.QM31)
    (range : DigitRange10) :
    (do let first ← value_direct_stage9_{i:02} packed openings selectors (selector,range)
        value_direct_stage9_{j:02} packed openings selectors (selector,first.2)) = (do
      let next ← loop (usize_body (digit_source_step10 openings.{field} {offset}) 10#usize) (range,0#usize)
      .ok (selector,next)) := by
  rw [digit_loop_ten10,digit_source_stage_binding10_{i:02}]
  simp only [PV_B3P_Ordered227.bind_assoc,bind_tc_ok]
  conv_lhs => arg 2; intro next; rw [digit_source_stage_binding10_{j:02}]
  have partition := PV_B3P_Ordered227.append (digit_source_step10 openings.{field} {offset})
    [0#usize,1#usize,2#usize,3#usize,4#usize] [5#usize,6#usize,7#usize,8#usize,9#usize] range
  have lifted := congrArg (fun result => result >>= (fun next => Result.ok (selector,next))) partition
  exact (PV_B3P_Ordered227.bind_assoc
    (PV_B3P_Ordered227.fold (digit_source_step10 openings.{field} {offset}) [0#usize,1#usize,2#usize,3#usize,4#usize] range)
    (PV_B3P_Ordered227.fold (digit_source_step10 openings.{field} {offset}) [5#usize,6#usize,7#usize,8#usize,9#usize])
    (fun next => Result.ok (selector,next))).symm.trans lifted.symm
#print axioms digit_pair_loop_binding10_{region}
end PV_B3P_Binding10227
''';files[f'PV_B3P_DigitPair10{region}227']=s
for m,s in files.items():
 p=L/(m+'.lean')
 if '--check'in sys.argv:assert p.read_text()==s,m
 else:p.write_text(s)
record=dict(modules=list(files),scope='three original source while loops, actual six direct-read emitted stages, ordered usize counters, all Result tags',semantic_use='reclassification within existing Charon/Aeneas tool trust')
p=O/'digit-loop-bindings.json'
if '--check'in sys.argv:assert json.loads(p.read_text())==record
else:p.write_text(json.dumps(record,indent=2)+'\n')
