"""Connect the emitted storage law to all nine complete-Result cell laws."""
from pathlib import Path
import json,sys
D=Path('evidence/pv-b3p6-20261028');L=D/'lean';O=D/'resume10'
params='''(sums : Array (Array U64 3#usize) 3#usize)
    (right : aspis_core.field.QM31) (left : reference_field.PreparedQm31Multiplier)'''
s='''import PV_B3P_MatrixStorage10227
import PV_B3P_MatrixStores9227
namespace PV_B3P_Binding10227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227
set_option autoImplicit false
'''
s+=f'\ndef accumulate_nine_cells10 {params} : Result Matrix3x3 := do\n'
s+='''  let right_sum ← aspis_core.field.CM31.add right.c0 right.c1
  let m ← aspis_core.field.M31.add right.c0.a right.c0.b
  let m1 ← aspis_core.field.M31.add right.c1.a right.c1.b
  let m2 ← aspis_core.field.M31.add right_sum.a right_sum.b
  let channels := Array.make 3#usize [
    Array.make 3#usize [right.c0.a,right.c0.b,m] (by simp),
    Array.make 3#usize [right.c1.a,right.c1.b,m1] (by simp),
    Array.make 3#usize [right_sum.a,right_sum.b,m2] (by simp)] (by simp)
'''
prev='sums'
for i in range(9):
 c,k=divmod(i,3);v=f'sums_{i}';s+=f'  let {v} ← matrix_cell {prev} {c}#usize {k}#usize (get3_{k} (get3_{c} left.components)) (get3_{k} (get3_{c} channels))\n';prev=v
s+='  .ok '+prev+'\n'
s+='\nattribute [local irreducible] aspis_core.field.CM31.add aspis_core.field.M31.add UScalar.cast U64.wrapping_add U64.wrapping_mul Aeneas.Std.Array.set\n'
s+=f'''\ntheorem accumulate_pure_nine_cells10 {params} :
    accumulate_pure_storage10 sums right left = accumulate_nine_cells10 sums right left := by
  unfold accumulate_pure_storage10 accumulate_nine_cells10
'''
for name in ['right_sum','m','m1','m2']:s+='  apply bind_equal9\n  intro '+name+'\n'
s+='  conv_rhs => simp only ['+', '.join(f'accumulation_store9_{c}_{k}'for c in range(3)for k in range(3))+',bind_tc_ok]\n'
s+='  unfold matrix_put get3_0 get3_1 get3_2\n  rfl\n'
s+=f'''\ntheorem accumulate_nine_cell_binding10 {params} :
    reference_field.accumulate_prepared227 sums right left = accumulate_nine_cells10 sums right left :=
  (accumulate_storage_binding10 sums right left).trans (accumulate_pure_nine_cells10 sums right left)
#print axioms accumulate_pure_nine_cells10
#print axioms accumulate_nine_cell_binding10
end PV_B3P_Binding10227
'''
p=L/'PV_B3P_MatrixModel10227.lean'
if '--check'in sys.argv:assert p.read_text()==s
else:p.write_text(s)
