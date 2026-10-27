import R1Z.ProverRwP7CurrentBaseBridge
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_CurrentNeg
open Aeneas Aeneas.Std Result
abbrev source := ProverRwP7CurrentFieldSource.aspis_core.field.M31.neg
theorem mask_true (x : U32) :
    x &&& core.num.U32.wrapping_sub 0#u32 (UScalar.cast_fromBool .U32 true) = x := by
  change x &&& 4294967295#u32 = x
  rw [UScalar.eq_equiv_bv_eq]
  exact BitVec.and_allOnes
theorem mask_false (x : U32) :
    x &&& core.num.U32.wrapping_sub 0#u32 (UScalar.cast_fromBool .U32 false) = 0#u32 := by
  change x &&& 0#u32 = 0#u32
  exact U32.and_zero x
theorem native (x : U32) : source x = AspisR1ProducerRelease47.field.M31.neg x := by
  unfold source ProverRwP7CurrentFieldSource.aspis_core.field.M31.neg
    ProverRwP7CurrentFieldSource.aspis_core.field.ct.neg
  simp only [lift,bind_tc_ok]
  by_cases h : x = 0#u32
  · subst x
    rw [show (0#u32 != 0#u32) = false from rfl,mask_false]
    rfl
  · have b : (x != 0#u32) = true := by simp [h]
    rw [b,mask_true]
    simp only [AspisR1ProducerRelease47.field.M31.neg,if_neg h,lift,bind_tc_ok]
    rw [ProverRwP7CurrentCtApi.sub,
      ProverRwP7CurrentFieldSource.aspis_core.field.P,
      AspisR1ProducerRelease47.field.P]
#print axioms mask_true
#print axioms mask_false
#print axioms native
end R1Z.PV_CB_CurrentNeg
