import R1Z.ProverRwSuccessNativePorts
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwSuccessCtSubtract
open Aeneas Aeneas.Std Result
abbrev source := ProverRwSuccessNativePorts.aspis_core.field.ct.subtract_p
abbrev p := AspisR1ProducerRelease47.field.P
theorem mask_true :
    p &&& core.num.U32.wrapping_sub 0#u32 (UScalar.cast_fromBool .U32 true)=p := by
  unfold p
  rw [AspisR1ProducerRelease47.field.P]
  rfl
theorem mask_false :
    p &&& core.num.U32.wrapping_sub 0#u32 (UScalar.cast_fromBool .U32 false)=0#u32 := by
  unfold p
  rw [AspisR1ProducerRelease47.field.P]
  rfl
theorem sub_zero (x : U32) : core.num.U32.wrapping_sub x 0#u32=x := by
  apply UScalar.eq_of_val_eq
  rw [core.num.U32.wrapping_sub_val_eq]
  simp only [show (0#u32).val=0 from rfl,Nat.sub_zero,Nat.add_mod_right]
  rw [UScalar.size]
  exact Nat.mod_eq_of_lt x.hBounds
theorem subtract (x : U32) :
    source x=.ok (if x≥p then U32.wrapping_sub x p else x) := by
  unfold source ProverRwSuccessNativePorts.aspis_core.field.ct.subtract_p
  simp only [ProverRwSuccessNativePorts.aspis_core.field.P,lift,bind_tc_ok]
  by_cases h : x≥p
  · simp only [h,decide_true,if_pos,mask_true]
    rfl
  · simp only [h,decide_false,if_neg,mask_false,sub_zero]
    rfl
#print axioms mask_true
#print axioms mask_false
#print axioms sub_zero
#print axioms subtract
end R1Z.ProverRwSuccessCtSubtract
