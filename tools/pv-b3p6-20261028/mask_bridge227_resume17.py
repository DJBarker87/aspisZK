"""Aggregate finite symbolic mask cells; external laws remain explicit."""
from pathlib import Path
masks=[1749,2048,2049,4097,6144,6145,26214];cells={};paths={}
for mask in masks:
 m=mask;path=[]
 while m:
  i=(m&-m).bit_length()-1;path.append(m);cells[m]=i;m&=m-1
 paths[mask]=path
s='\n'.join(f'import PV_B3P_DirectMask17_{m}227'for m in masks)+'\n'
s+='''namespace PV_B3P_Direct17227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Success227 PV_B3P_Correct14227 Result
set_option autoImplicit false

/-- These are outstanding source laws for the two extracted externals.
This structure is not installed as a native instance or an endpoint premise. -/
structure MaskIntegerLaws17 (ones zeros : U16 → Result U32) : Prop where
'''
for m in masks:s+=f'  count_{m} : ones {m}#u16 = .ok {len(paths[m])}#u32\n'
for m,i in sorted(cells.items()):s+=f'  trail_{m} : zeros {m}#u16 = .ok {i}#u32\n'
s+='''
theorem mask_extraction_reference_on_domain17 (ones zeros : U16 → Result U32)
    (laws : MaskIntegerLaws17 ones zeros)
    (values : Array aspis_core.field.QM31 16#usize) (mask : U16)
    (allowed : MaskAllowed mask) :
    host_copy_terminal.selector_mask_sum_16 ones zeros values mask =
      reference_copy_terminal.selector_mask_sum_16 values mask := by
  rcases allowed with h|h|h|h|h|h|h
'''
for m in masks:
 s+=f'  · subst mask\n    exact mask_direct17_{m} ones zeros values laws.count_{m}'
 for c in paths[m]:s+=f' laws.trail_{c}'
 s+='\n'
s+='''
def mask_ones_model17 (mask : U16) : Result U32 :=
'''
for m in masks:s+=f'  if mask = {m}#u16 then .ok {len(paths[m])}#u32 else\n'
s+='  .ok 0#u32\n\ndef mask_zeros_model17 (mask : U16) : Result U32 :=\n'
for m,i in sorted(cells.items()):s+=f'  if mask = {m}#u16 then .ok {i}#u32 else\n'
s+='''  .ok 0#u32

/-- Consistency only. This finite mathematical model does not bind the Rust
intrinsics, and earns no native source-law credit. -/
theorem mask_integer_laws_consistent17 :
    MaskIntegerLaws17 mask_ones_model17 mask_zeros_model17 := by
  constructor <;> rfl

#print axioms mask_extraction_reference_on_domain17
#print axioms mask_integer_laws_consistent17
end PV_B3P_Direct17227
'''
Path('evidence/pv-b3p6-20261028/lean/PV_B3P_DirectMaskBridge17227.lean').write_text(s)
