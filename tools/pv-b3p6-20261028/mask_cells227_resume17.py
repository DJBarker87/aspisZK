"""Emit one small bit-control cell per actual mask, with external laws explicit."""
from pathlib import Path
D=Path('evidence/pv-b3p6-20261028/lean')
for mask in [2048,2049,4097,6144,6145,1749,26214]:
 cells=[];m=mask
 while m:
  i=(m&-m).bit_length()-1;n=m&(m-1);cells.append((m,i,n));m=n
 s=f'''import PV_B3P_DirectMask17227
import PV_B3P_MaskBody10_{mask}227
namespace PV_B3P_Direct17227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding10227 Result
set_option autoImplicit false
attribute [local irreducible] Array.index_usize aspis_core.field.QM31.add
'''
 for m,i,n in cells:
  s+=f'theorem mask_clear17_{m} : ({m}#u16 &&& (U16.wrapping_sub {m}#u16 1#u16)) = {n}#u16 := by rfl\n' if m==mask else ''
 # Shared cells are local have facts, avoiding cross-chunk duplicate names.
 s+=f'''theorem mask_direct17_{mask} (ones zeros : U16 → Result U32)
    (values : Array aspis_core.field.QM31 16#usize)
    (count_law : ones {mask}#u16 = .ok {len(cells)}#u32)
'''
 for m,i,n in cells:s+=f'    (trail_{m} : zeros {m}#u16 = .ok {i}#u32)\n'
 s+=f'''    : host_copy_terminal.selector_mask_sum_16 ones zeros values {mask}#u16 =
      reference_copy_terminal.selector_mask_sum_16 values {mask}#u16 := by
  rw [mask_entry17 ones zeros values {mask}#u16 {len(cells)}#u32 count_law (by scalar_tac)]
  rw [mask_body_binding10_{mask},PV_B3P_Mask227.result_{mask}]
'''
 for m,i,n in cells:
  s+=f'''  have clear_{m} : ({m}#u16 &&& (U16.wrapping_sub {m}#u16 1#u16)) = {n}#u16 := by rfl
  have step_{m} (sum : aspis_core.field.QM31) :=
    mask_loop_step17 zeros values {m}#u16 sum {i}#u32 (by decide) trail_{m}
'''
 s+='  simp only ['+','.join(f'step_{m},clear_{m}'for m,_,_ in cells)+',mask_loop_stop17]\n'
 for i in sorted({i for _,i,_ in cells}):
  s+=f'  have cast_{i} : UScalar.cast .Usize {i}#u32 = {i}#usize := by scalar_tac\n'
 s+='  simp only [mask_add17,mask_step10,mask_read10,'+','.join(f'cast_{i}'for i in sorted({i for _,i,_ in cells}))+']\n'
 s+='  rfl\n'+f'#print axioms mask_direct17_{mask}\nend PV_B3P_Direct17227\n'
 (D/f'PV_B3P_DirectMask17_{mask}227.lean').write_text(s)
