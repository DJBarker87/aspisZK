"""Generate small source-wrapper laws, with intrinsics explicitly at V370.
No template axioms or finite lookup interpretation. Sixteen-bit reduction only.
"""
from pathlib import Path
import json
D=Path('evidence/pv-b3p6-20261028');R=D/'resume17'
fields=json.loads((R/'MASK-EXTERNAL-AUTHORITY-D540.json').read_text())['fields']
s='''import PV_B3P_DirectMaskBridge17227
namespace PV_B3P_MaskSource542227
open Aeneas Aeneas.Std PV_B3P_Direct17227
set_option autoImplicit false

/-- Mathematical ctpop specification. Compiler implementation is V370,
D381/D386, not a new native axiom or trust-list field. -/
def ctpop16_spec542 (bits : BitVec 16) : BitVec 32 := bits.cpop.zeroExtend 32
/-- Mathematical cttz specification, including zero -> 16 (not cttz_nonzero).
Compiler implementation is retained V370 / D381,D386. -/
def cttz16_spec542 (bits : BitVec 16) : BitVec 32 := bits.ctz.zeroExtend 32

/-- Exact ordinary source wrapper: return intrinsics::ctpop(self). -/
def count_ones_source542 (value : U16) : Result U32 := .ok ⟨ctpop16_spec542 value.bv⟩
/-- Exact ordinary source wrapper: return intrinsics::cttz(self). -/
def trailing_zeros_source542 (value : U16) : Result U32 := .ok ⟨cttz16_spec542 value.bv⟩

theorem count_ones_source_step542 (value : U16) :
    count_ones_source542 value = .ok ⟨ctpop16_spec542 value.bv⟩ := rfl
theorem trailing_zeros_source_step542 (value : U16) :
    trailing_zeros_source542 value = .ok ⟨cttz16_spec542 value.bv⟩ := rfl

-- Every cell is at most sixteen bits, with a reduction graph bounded by 16.
-- These are intrinsic specification equations, never a field/range replay.
'''
for name,prop in fields:
 prop=prop.replace('ones ','count_ones_source542 ').replace('zeros ','trailing_zeros_source542 ')
 s+=f'theorem {name}_source542 : {prop} := by rfl\n'
s+='''
theorem count_zero_source542 : count_ones_source542 0#u16 = .ok 0#u32 := rfl
theorem trailing_zero_source542 : trailing_zeros_source542 0#u16 = .ok 16#u32 := rfl

theorem mask_integer_source_laws542 :
    MaskIntegerLaws17 count_ones_source542 trailing_zeros_source542 := by
  exact ⟨'''+','.join(n+'_source542'for n,_ in fields)+'''⟩

#print axioms count_ones_source_step542
#print axioms trailing_zeros_source_step542
#print axioms count_zero_source542
#print axioms trailing_zero_source542
#print axioms mask_integer_source_laws542
end PV_B3P_MaskSource542227
'''
(D/'lean/PV_B3P_MaskSource542227.lean').write_text(s)
