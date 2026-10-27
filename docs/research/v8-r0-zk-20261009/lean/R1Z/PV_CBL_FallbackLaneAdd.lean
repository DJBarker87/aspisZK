import R1Z.PV_CBL_FallbackSchedule
import R1Z.PV_CBL_FallbackArray4
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_FallbackLaneAdd
open PV_CBL_FallbackArray4
set_option autoImplicit false
theorem shape (a0 a1 a2 a3 b0 b1 b2 b3 : U32) :
    PV_CBL_FallbackSchedule.sha_fallback_reference.add
      (pack a0 a1 a2 a3) (pack b0 b1 b2 b3) =
      ok (pack (U32.wrapping_add a0 b0) (U32.wrapping_add a1 b1) (U32.wrapping_add a2 b2) (U32.wrapping_add a3 b3)) := by
  simp only [PV_CBL_FallbackSchedule.sha_fallback_reference.add,index0,index1,index2,index3,lift,bind_tc_ok]
  rfl
#print axioms shape
end R1Z.PV_CBL_FallbackLaneAdd
