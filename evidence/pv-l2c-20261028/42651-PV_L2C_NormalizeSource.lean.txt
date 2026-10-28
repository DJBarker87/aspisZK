import PV_L2C_ReferenceArithmetic
import PV_L2C_SubPrimitive
set_option autoImplicit false
namespace PV_L2C_NormalizeSource
open Aeneas Aeneas.Std Result AspisR1ProverBalance9 PV_L2C_ReferenceArithmetic

/-- The exact final comparison/subtraction cut common to both extracted ops. -/
def normalize (s : U32) : Result U32 :=
  if s≥aspis_core.field.P then ok (U32.wrapping_sub s aspis_core.field.P) else ok s

theorem wrap_eta (s : U32) : wrap s.bv=s := by cases s; rfl
#print axioms wrap_eta

theorem modulus : aspis_core.field.P=wrap (BitVec.ofNat 32 PV_L2C_M31.p) := by
  unfold aspis_core.field.P
  rfl
#print axioms modulus

theorem normalize_native (s : U32) :
    normalize s=ok (wrap (PV_L2C_M31.subtractP s.bv)) := by
  rw [PV_L2C_M31.subtractP_branch]
  have hc : (s≥aspis_core.field.P) ↔ PV_L2C_M31.p≤s.bv.toNat := by
    rw [modulus]
    rfl
  unfold normalize
  by_cases h : s≥aspis_core.field.P
  · rw [if_pos h,if_pos (hc.mp h),modulus,PV_L2C_SubPrimitive.wrapped_sub]
    rfl
  · rw [if_neg h,if_neg (fun h' => h (hc.mpr h')),wrap_eta]
#print axioms normalize_native

theorem sub_input (x y : U32) :
    (U32.wrapping_sub (U32.wrapping_add x aspis_core.field.P) y).bv=
      x.bv+BitVec.ofNat 32 PV_L2C_M31.p-y.bv := by
  rw [modulus,PV_L2C_SubPrimitive.wrapped_add,PV_L2C_SubPrimitive.wrapped_sub]
  rfl
#print axioms sub_input

theorem sub_cut (x y : U32) :
    aspis_core.field.M31.sub x y=
      normalize (U32.wrapping_sub (U32.wrapping_add x aspis_core.field.P) y) := by
  unfold aspis_core.field.M31.sub
  generalize U32.wrapping_add x aspis_core.field.P = a
  simp only [lift,bind_tc_ok]
  generalize U32.wrapping_sub a y = b
  rfl
#print axioms sub_cut
end PV_L2C_NormalizeSource
