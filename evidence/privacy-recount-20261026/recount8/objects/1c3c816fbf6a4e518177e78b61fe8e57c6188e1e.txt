import R1Z.PV_RDB2C_PV_B2_C_RawWeights251Funs
import R1Z.PV_RDB2C_PV_B2_D_SmallScalar
set_option autoImplicit false
namespace PV_B2_D_RowSource
open Aeneas Aeneas.Std Result ControlFlow PV_B2_251c1
theorem tau0 : Array.index_usize transport.TAU 0#usize = ok 3#usize := by
  unfold transport.TAU
  rfl
def digit0 (j : Usize) : Usize :=
  Usize.wrapping_shl (Usize.wrapping_shr j 0#u32 &&& 3#usize) 6#u32
theorem body0 (j out : Usize) : host_weights.host_row_loop0.body j out 0#usize =
    ok (cont (out ||| digit0 j,1#usize)) := by
  unfold host_weights.host_row_loop0.body digit0
  simp only [show (0#usize < 5#usize) from by decide,if_pos,lift,bind_tc_ok,tau0]
  simp only [show UScalar.cast .U32 (Usize.wrapping_mul 2#usize 0#usize) = 0#u32 from by
      apply UScalar.eq_of_val_eq
      rw [PV_B2_D_SmallScalar.cast_val,PV_B2_D_SmallScalar.mul_val _ _ (by scalar_tac)]
      scalar_tac,
    show UScalar.cast .U32 (Usize.wrapping_mul 2#usize 3#usize) = 6#u32 from by
      apply UScalar.eq_of_val_eq
      rw [PV_B2_D_SmallScalar.cast_val,PV_B2_D_SmallScalar.mul_val _ _ (by scalar_tac)]
      scalar_tac,
    show Usize.wrapping_add 0#usize 1#usize = 1#usize from by
      apply UScalar.eq_of_val_eq
      rw [PV_B2_D_SmallScalar.add_val _ _ (by scalar_tac)]
      scalar_tac]
#print axioms tau0
#print axioms body0
theorem tau1 : Array.index_usize transport.TAU 1#usize = ok 4#usize := by
  unfold transport.TAU
  rfl
def digit1 (j : Usize) : Usize :=
  Usize.wrapping_shl (Usize.wrapping_shr j 2#u32 &&& 3#usize) 8#u32
theorem body1 (j out : Usize) : host_weights.host_row_loop0.body j out 1#usize =
    ok (cont (out ||| digit1 j,2#usize)) := by
  unfold host_weights.host_row_loop0.body digit1
  simp only [show (1#usize < 5#usize) from by decide,if_pos,lift,bind_tc_ok,tau1]
  simp only [show UScalar.cast .U32 (Usize.wrapping_mul 2#usize 1#usize) = 2#u32 from by
      apply UScalar.eq_of_val_eq
      rw [PV_B2_D_SmallScalar.cast_val,PV_B2_D_SmallScalar.mul_val _ _ (by scalar_tac)]
      scalar_tac,
    show UScalar.cast .U32 (Usize.wrapping_mul 2#usize 4#usize) = 8#u32 from by
      apply UScalar.eq_of_val_eq
      rw [PV_B2_D_SmallScalar.cast_val,PV_B2_D_SmallScalar.mul_val _ _ (by scalar_tac)]
      scalar_tac,
    show Usize.wrapping_add 1#usize 1#usize = 2#usize from by
      apply UScalar.eq_of_val_eq
      rw [PV_B2_D_SmallScalar.add_val _ _ (by scalar_tac)]
      scalar_tac]
#print axioms tau1
#print axioms body1
theorem tau2 : Array.index_usize transport.TAU 2#usize = ok 2#usize := by
  unfold transport.TAU
  rfl
def digit2 (j : Usize) : Usize :=
  Usize.wrapping_shl (Usize.wrapping_shr j 4#u32 &&& 3#usize) 4#u32
theorem body2 (j out : Usize) : host_weights.host_row_loop0.body j out 2#usize =
    ok (cont (out ||| digit2 j,3#usize)) := by
  unfold host_weights.host_row_loop0.body digit2
  simp only [show (2#usize < 5#usize) from by decide,if_pos,lift,bind_tc_ok,tau2]
  simp only [show UScalar.cast .U32 (Usize.wrapping_mul 2#usize 2#usize) = 4#u32 from by
      apply UScalar.eq_of_val_eq
      rw [PV_B2_D_SmallScalar.cast_val,PV_B2_D_SmallScalar.mul_val _ _ (by scalar_tac)]
      scalar_tac,
    show UScalar.cast .U32 (Usize.wrapping_mul 2#usize 2#usize) = 4#u32 from by
      apply UScalar.eq_of_val_eq
      rw [PV_B2_D_SmallScalar.cast_val,PV_B2_D_SmallScalar.mul_val _ _ (by scalar_tac)]
      scalar_tac,
    show Usize.wrapping_add 2#usize 1#usize = 3#usize from by
      apply UScalar.eq_of_val_eq
      rw [PV_B2_D_SmallScalar.add_val _ _ (by scalar_tac)]
      scalar_tac]
#print axioms tau2
#print axioms body2
theorem tau3 : Array.index_usize transport.TAU 3#usize = ok 0#usize := by
  unfold transport.TAU
  rfl
def digit3 (j : Usize) : Usize :=
  Usize.wrapping_shl (Usize.wrapping_shr j 6#u32 &&& 3#usize) 0#u32
theorem body3 (j out : Usize) : host_weights.host_row_loop0.body j out 3#usize =
    ok (cont (out ||| digit3 j,4#usize)) := by
  unfold host_weights.host_row_loop0.body digit3
  simp only [show (3#usize < 5#usize) from by decide,if_pos,lift,bind_tc_ok,tau3]
  simp only [show UScalar.cast .U32 (Usize.wrapping_mul 2#usize 3#usize) = 6#u32 from by
      apply UScalar.eq_of_val_eq
      rw [PV_B2_D_SmallScalar.cast_val,PV_B2_D_SmallScalar.mul_val _ _ (by scalar_tac)]
      scalar_tac,
    show UScalar.cast .U32 (Usize.wrapping_mul 2#usize 0#usize) = 0#u32 from by
      apply UScalar.eq_of_val_eq
      rw [PV_B2_D_SmallScalar.cast_val,PV_B2_D_SmallScalar.mul_val _ _ (by scalar_tac)]
      scalar_tac,
    show Usize.wrapping_add 3#usize 1#usize = 4#usize from by
      apply UScalar.eq_of_val_eq
      rw [PV_B2_D_SmallScalar.add_val _ _ (by scalar_tac)]
      scalar_tac]
#print axioms tau3
#print axioms body3
theorem tau4 : Array.index_usize transport.TAU 4#usize = ok 1#usize := by
  unfold transport.TAU
  rfl
def digit4 (j : Usize) : Usize :=
  Usize.wrapping_shl (Usize.wrapping_shr j 8#u32 &&& 3#usize) 2#u32
theorem body4 (j out : Usize) : host_weights.host_row_loop0.body j out 4#usize =
    ok (cont (out ||| digit4 j,5#usize)) := by
  unfold host_weights.host_row_loop0.body digit4
  simp only [show (4#usize < 5#usize) from by decide,if_pos,lift,bind_tc_ok,tau4]
  simp only [show UScalar.cast .U32 (Usize.wrapping_mul 2#usize 4#usize) = 8#u32 from by
      apply UScalar.eq_of_val_eq
      rw [PV_B2_D_SmallScalar.cast_val,PV_B2_D_SmallScalar.mul_val _ _ (by scalar_tac)]
      scalar_tac,
    show UScalar.cast .U32 (Usize.wrapping_mul 2#usize 1#usize) = 2#u32 from by
      apply UScalar.eq_of_val_eq
      rw [PV_B2_D_SmallScalar.cast_val,PV_B2_D_SmallScalar.mul_val _ _ (by scalar_tac)]
      scalar_tac,
    show Usize.wrapping_add 4#usize 1#usize = 5#usize from by
      apply UScalar.eq_of_val_eq
      rw [PV_B2_D_SmallScalar.add_val _ _ (by scalar_tac)]
      scalar_tac]
#print axioms tau4
#print axioms body4
theorem end_body (j out : Usize) : host_weights.host_row_loop0.body j out 5#usize = ok (done out) := by
  unfold host_weights.host_row_loop0.body
  simp only [show ¬ (5#usize < 5#usize) from by decide,if_false]
def suffix5 (_j out : Usize) : Usize := out
theorem source5 (j out : Usize) : host_weights.host_row_loop0 j out 5#usize = ok (suffix5 j out) := by
  unfold host_weights.host_row_loop0
  rw [Aeneas.Std.loop.eq_def]
  simp only [end_body,bind_tc_ok,suffix5]
#print axioms end_body
#print axioms source5
def suffix4 (j out : Usize) : Usize := suffix5 j (out ||| digit4 j)
theorem source4 (j out : Usize) : host_weights.host_row_loop0 j out 4#usize = ok (suffix4 j out) := by
  unfold host_weights.host_row_loop0
  rw [Aeneas.Std.loop.eq_def]
  simp only [body4,bind_tc_ok]
  change host_weights.host_row_loop0 j (out ||| digit4 j) 5#usize = _
  exact source5 j (out ||| digit4 j)
#print axioms source4
def suffix3 (j out : Usize) : Usize := suffix4 j (out ||| digit3 j)
theorem source3 (j out : Usize) : host_weights.host_row_loop0 j out 3#usize = ok (suffix3 j out) := by
  unfold host_weights.host_row_loop0
  rw [Aeneas.Std.loop.eq_def]
  simp only [body3,bind_tc_ok]
  change host_weights.host_row_loop0 j (out ||| digit3 j) 4#usize = _
  exact source4 j (out ||| digit3 j)
#print axioms source3
def suffix2 (j out : Usize) : Usize := suffix3 j (out ||| digit2 j)
theorem source2 (j out : Usize) : host_weights.host_row_loop0 j out 2#usize = ok (suffix2 j out) := by
  unfold host_weights.host_row_loop0
  rw [Aeneas.Std.loop.eq_def]
  simp only [body2,bind_tc_ok]
  change host_weights.host_row_loop0 j (out ||| digit2 j) 3#usize = _
  exact source3 j (out ||| digit2 j)
#print axioms source2
def suffix1 (j out : Usize) : Usize := suffix2 j (out ||| digit1 j)
theorem source1 (j out : Usize) : host_weights.host_row_loop0 j out 1#usize = ok (suffix1 j out) := by
  unfold host_weights.host_row_loop0
  rw [Aeneas.Std.loop.eq_def]
  simp only [body1,bind_tc_ok]
  change host_weights.host_row_loop0 j (out ||| digit1 j) 2#usize = _
  exact source2 j (out ||| digit1 j)
#print axioms source1
def suffix0 (j out : Usize) : Usize := suffix1 j (out ||| digit0 j)
theorem source0 (j out : Usize) : host_weights.host_row_loop0 j out 0#usize = ok (suffix0 j out) := by
  unfold host_weights.host_row_loop0
  rw [Aeneas.Std.loop.eq_def]
  simp only [body0,bind_tc_ok]
  change host_weights.host_row_loop0 j (out ||| digit0 j) 1#usize = _
  exact source1 j (out ||| digit0 j)
#print axioms source0
theorem loops_eq (j out d : Usize) :
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
