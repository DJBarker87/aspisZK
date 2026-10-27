import R1Z.PV_CBL_FallbackSchedule
import R1Z.PV_CBL_FallbackArray4
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_FallbackLaneLeft
open PV_CBL_FallbackArray4
set_option autoImplicit false
theorem shape (a0 a1 a2 a3 o : U32) :
    PV_CBL_FallbackSchedule.sha_fallback_reference.shr (pack a0 a1 a2 a3) o =
      ok (pack (U32.wrapping_shl a0 o) (U32.wrapping_shl a1 o) (U32.wrapping_shl a2 o) (U32.wrapping_shl a3 o)) := by
  simp only [PV_CBL_FallbackSchedule.sha_fallback_reference.shr,index0,index1,index2,index3,lift,bind_tc_ok]
  rfl
#print axioms shape
end R1Z.PV_CBL_FallbackLaneLeft
