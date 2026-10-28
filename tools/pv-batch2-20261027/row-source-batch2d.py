"""Symbolic five-digit row permutation; fixed small TAU reads, no table reduction."""
from pathlib import Path
import sys
L=Path('docs/research/v8-r0-zk-20261009/lean/R1Z');s='''import R1Z.PV_B2_C_RawWeights251Funs
import R1Z.PV_B2_D_SmallScalar
set_option autoImplicit false
namespace PV_B2_D_RowSource
open Aeneas Aeneas.Std Result ControlFlow PV_B2_251c1
'''
for d,v in enumerate([3,4,2,0,1]):
 s+=f'''theorem tau{d} : Array.index_usize transport.TAU {d}#usize = ok {v}#usize := by
  unfold transport.TAU
  rfl
def digit{d} (j : Usize) : Usize :=
  Usize.wrapping_shl (Usize.wrapping_shr j {2*d}#u32 &&& 3#usize) {2*v}#u32
theorem body{d} (j out : Usize) : host_weights.host_row_loop0.body j out {d}#usize =
    ok (cont (out ||| digit{d} j,{d+1}#usize)) := by
  unfold host_weights.host_row_loop0.body digit{d}
  simp only [show ({d}#usize < 5#usize) from by decide,if_pos,lift,bind_tc_ok,tau{d}]
  simp only [show UScalar.cast .U32 (Usize.wrapping_mul 2#usize {d}#usize) = {2*d}#u32 from by
      apply UScalar.eq_of_val_eq
      rw [PV_B2_D_SmallScalar.cast_val,PV_B2_D_SmallScalar.mul_val _ _ (by scalar_tac)]
      scalar_tac,
    show UScalar.cast .U32 (Usize.wrapping_mul 2#usize {v}#usize) = {2*v}#u32 from by
      apply UScalar.eq_of_val_eq
      rw [PV_B2_D_SmallScalar.cast_val,PV_B2_D_SmallScalar.mul_val _ _ (by scalar_tac)]
      scalar_tac,
    show Usize.wrapping_add {d}#usize 1#usize = {d+1}#usize from by
      apply UScalar.eq_of_val_eq
      rw [PV_B2_D_SmallScalar.add_val _ _ (by scalar_tac)]
      scalar_tac]
#print axioms tau{d}
#print axioms body{d}
'''
s+='''theorem end_body (j out : Usize) : host_weights.host_row_loop0.body j out 5#usize = ok (done out) := by
  unfold host_weights.host_row_loop0.body
  simp only [show ¬ (5#usize < 5#usize) from by decide,if_false]
def suffix5 (_j out : Usize) : Usize := out
theorem source5 (j out : Usize) : host_weights.host_row_loop0 j out 5#usize = ok (suffix5 j out) := by
  unfold host_weights.host_row_loop0
  rw [Aeneas.Std.loop.eq_def]
  simp only [end_body,bind_tc_ok,suffix5]
#print axioms end_body
#print axioms source5
'''
for d in reversed(range(5)):
 s+=f'''def suffix{d} (j out : Usize) : Usize := suffix{d+1} j (out ||| digit{d} j)
theorem source{d} (j out : Usize) : host_weights.host_row_loop0 j out {d}#usize = ok (suffix{d} j out) := by
  unfold host_weights.host_row_loop0
  rw [Aeneas.Std.loop.eq_def]
  simp only [body{d},bind_tc_ok]
  change host_weights.host_row_loop0 j (out ||| digit{d} j) {d+1}#usize = _
  exact source{d+1} j (out ||| digit{d} j)
#print axioms source{d}
'''
s+='''theorem loops_eq (j out d : Usize) :
    host_weights.host_row_loop1 j out d = host_weights.host_row_loop0 j out d := by rfl

theorem S1 (j : Usize) : host_weights.host_row .S1 j = ok (suffix0 j 0#usize) := by
  exact source0 j 0#usize

theorem S2 (j : Usize) : host_weights.host_row .S2 j = ok (suffix0 j 0#usize) := by
  unfold host_weights.host_row
  rw [loops_eq,source0]
#print axioms loops_eq
#print axioms S1
#print axioms S2
end PV_B2_D_RowSource
'''
p=L/'PV_B2_D_RowSource.lean'
if '--check' in sys.argv:assert p.read_text()==s
else:p.write_text(s)
