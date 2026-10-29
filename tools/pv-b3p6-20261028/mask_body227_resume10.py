"""Apply the seven accepted sparse-mask walk laws to the actual emitted body."""
from pathlib import Path
import json,sys
D=Path('evidence/pv-b3p6-20261028');L=D/'lean';O=D/'resume10';files={}
header='''namespace PV_B3P_Binding10227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227
set_option autoImplicit false
'''
s='import PV_B3P_E227_12\nimport PV_B3P_Mask227\nimport PV_B3P_NineUnroll9227\n'+header
s+='\ndef mask_read10 (values : Array aspis_core.field.QM31 16#usize) : Nat → Result aspis_core.field.QM31\n'
for i in range(16):s+=f'  | {i} => Array.index_usize values {i}#usize\n'
s+='  | _ => .fail Error.arrayOutOfBounds\n'
s+='''
def mask_step10 (values : Array aspis_core.field.QM31 16#usize)
    (sum : aspis_core.field.QM31) (index : Nat) : Result aspis_core.field.QM31 := do
  let value ← mask_read10 values index
  aspis_core.field.QM31.add sum value
end PV_B3P_Binding10227
''';files['PV_B3P_MaskBodyStep10227']=s
rows=[]
for mask in [1749,2048,2049,4097,6144,6145,26214]:
 s='import PV_B3P_MaskBodyStep10227\n'+header
 s+='\nattribute [local irreducible] Array.index_usize aspis_core.field.QM31.add\n'
 s+=f'''\ntheorem mask_body_binding10_{mask} (values : Array aspis_core.field.QM31 16#usize) :
    reference_copy_terminal.selector_mask_sum_16 values {mask}#u16 =
      PV_B3P_Mask227.foldResult (mask_step10 values) (PV_B3P_Mask227.walk 16 {mask}) aspis_core.field.QM31.ZERO := by
  rw [PV_B3P_Mask227.result_{mask}]
  conv_rhs => simp only [mask_step10,mask_read10,PV_B3P_Ordered227.bind_assoc,bind_tc_ok,result_right]
  all_goals rfl
#print axioms mask_body_binding10_{mask}
end PV_B3P_Binding10227
'''
 m=f'PV_B3P_MaskBody10_{mask}227';files[m]=s;rows.append(dict(mask=mask,module=m,theorem=f'mask_body_binding10_{mask}',complement_law=f'PV_B3P_Mask227.complement_off_{mask}',scope='this frozen mask only; not an arbitrary-mask body equivalence'))
for m,s in files.items():
 p=L/(m+'.lean')
 if '--check'in sys.argv:assert p.read_text()==s,m
 else:p.write_text(s)
record=dict(modules=list(files),applications=rows,credit='actual emitted mask-sum body at each of seven frozen masks to named source walk Result; caller reachability and std bit-operation association remain separate',semantic_use='reclassification within existing Charon/Aeneas tool trust')
p=O/'mask-body-bindings.json'
if '--check'in sys.argv:assert json.loads(p.read_text())==record
else:p.write_text(json.dumps(record,indent=2)+'\n')
