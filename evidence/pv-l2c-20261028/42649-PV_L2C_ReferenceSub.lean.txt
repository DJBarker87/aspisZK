import PV_L2C_ReferenceArithmetic
import PV_L2C_SubPrimitive
set_option autoImplicit false
namespace PV_L2C_ReferenceSub
open Aeneas Aeneas.Std Result AspisR1ProverBalance9 PV_L2C_ReferenceArithmetic

theorem modulus : aspis_core.field.P=wrap (BitVec.ofNat 32 PV_L2C_M31.p) := by
  unfold aspis_core.field.P
  rfl
#print axioms modulus

theorem m31_sub (x y : U32) :
    aspis_core.field.M31.sub x y=ok (wrap (PV_L2C_M31.sub x.bv y.bv)) := by
  let s := U32.wrapping_sub (U32.wrapping_add x aspis_core.field.P) y
  have hs : s.bv=x.bv+BitVec.ofNat 32 PV_L2C_M31.p-y.bv := by
    unfold s
    rw [modulus,PV_L2C_SubPrimitive.wrapped_add,PV_L2C_SubPrimitive.wrapped_sub]
    rfl
  have hc : (s≥aspis_core.field.P) ↔ PV_L2C_M31.p≤s.bv.toNat := by
    rw [modulus]
    rfl
  rw [PV_L2C_M31.sub,← hs,PV_L2C_M31.subtractP_branch]
  unfold aspis_core.field.M31.sub
  change (if s≥aspis_core.field.P then ok (U32.wrapping_sub s aspis_core.field.P) else ok s)=
    ok (wrap (if PV_L2C_M31.p≤s.bv.toNat then
      s.bv-BitVec.ofNat 32 PV_L2C_M31.p else s.bv))
  by_cases h : s≥aspis_core.field.P
  · rw [if_pos h,if_pos (hc.mp h),modulus,PV_L2C_SubPrimitive.wrapped_sub]
    rfl
  · rw [if_neg h,if_neg (fun h' => h (hc.mpr h'))]
    cases s
    rfl
#print axioms m31_sub
end PV_L2C_ReferenceSub
