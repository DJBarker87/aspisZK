import R1Z.PV_CBL_FallbackSchedule
import R1Z.PV_CBL_FallbackArray4
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_FallbackLaneLoad
open PV_CBL_FallbackArray4
set_option autoImplicit false
theorem shape (a0 a1 a2 a3 b0 b1 b2 b3 : U32) :
    PV_CBL_FallbackSchedule.sha_fallback_reference.sha256load
      (pack a0 a1 a2 a3) (pack b0 b1 b2 b3) = ok (pack b3 a0 a1 a2) := by
  simp only [PV_CBL_FallbackSchedule.sha_fallback_reference.sha256load,index0,index1,index2,index3,lift,bind_tc_ok]
  rfl
#print axioms shape
end R1Z.PV_CBL_FallbackLaneLoad
