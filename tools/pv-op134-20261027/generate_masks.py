from pathlib import Path
import re,sys
root=Path(__file__).resolve().parents[2];lean=root/'docs/research/v8-r0-zk-20261009/lean/R1Z'
t=(lean/'PV_CBM_MasksReference.lean').read_text();vs=list(map(int,re.findall(r'(\d+)#u16',t)))
assert len(vs)==64
s='''import R1Z.PV_CBM_MasksReference
namespace R1Z.PV_Op134_Masks
open Aeneas Aeneas.Std Result
set_option autoImplicit false
'''
s+='def masks : Array U16 64#usize := Array.make 64#usize ['+', '.join(str(v)+'#u16' for v in vs)+']\n'
s+='''theorem source : PV_CBM_ReferenceRaw.reference.masks = ok (.Ok masks) := rfl
theorem length : masks.val.length = 64 := rfl
#print axioms source
#print axioms length
end R1Z.PV_Op134_Masks
'''
outputs={'PV_Op134_Masks':s}
for i in range(8):
 mod=f'PV_Op134_MaskBits{i}'
 outputs[mod]=f'''import R1Z.PV_Op134_Masks
import R1Z.PV_Op134_RowSpec
namespace R1Z.{mod}
open Aeneas Aeneas.Std
set_option autoImplicit false
-- Only 8 blocks x 16 bit positions are evaluated; no large Finset.univ.
theorem bits : ∀ block : Fin 8, ∀ bit : Fin 16,
    Nat.testBit (PV_Op134_Masks.masks.val[{8*i}+block.val]'(by
      rw [PV_Op134_Masks.length]; have := block.isLt; omega)).val bit.val = true ↔
      16*({8*i}+block.val)+bit.val ∈ PV_Op134_RowSpec.rows.map (fun r => r.val) := by decide
#print axioms bits
end R1Z.{mod}
'''
check='--check' in sys.argv
for n,s in outputs.items():
 p=lean/(n+'.lean')
 if check:assert p.read_text()==s,n
 else:p.write_text(s)
print('CHECK' if check else 'GENERATED',len(outputs),'mask modules')
