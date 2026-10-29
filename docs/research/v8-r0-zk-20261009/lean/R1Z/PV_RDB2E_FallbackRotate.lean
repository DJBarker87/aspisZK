import R1Z.PV_RDB2E_FallbackLanes

section
-- Unchanged source component R1Z.PV_CBL_FallbackRotate
open Aeneas Aeneas.Std
namespace R1Z.PV_CBL_FallbackRotate
open PV_CBL_FallbackSmallSigma
set_option autoImplicit false
theorem right7 (x : U32) :
    U32.wrapping_shr x 7#u32 ||| U32.wrapping_shl x 25#u32 = core.num.U32.rotate_right x 7#u32 := by
  apply U32.bv_eq_imp_eq
  change (x.bv >>> 7) ||| (x.bv <<< 25) = x.bv.rotateRight 7
  rfl
theorem right18 (x : U32) :
    U32.wrapping_shr x 18#u32 ||| U32.wrapping_shl x 14#u32 = core.num.U32.rotate_right x 18#u32 := by
  apply U32.bv_eq_imp_eq
  change (x.bv >>> 18) ||| (x.bv <<< 14) = x.bv.rotateRight 18
  rfl
theorem small0_eq (x : U32) : small0 x =
    core.num.U32.rotate_right x 7#u32 ^^^ core.num.U32.rotate_right x 18#u32 ^^^ U32.wrapping_shr x 3#u32 := by
  simp only [small0,right7,right18]
#print axioms right7
#print axioms right18
#print axioms small0_eq
end R1Z.PV_CBL_FallbackRotate

end
