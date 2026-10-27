import R1Z.PV_CBL_FallbackSchedule
import R1Z.PV_CBL_FallbackArray4
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_FallbackLaneXor
open PV_CBL_FallbackArray4
set_option autoImplicit false
theorem shape (a0 a1 a2 a3 b0 b1 b2 b3 : U32) :
    PV_CBL_FallbackSchedule.sha_fallback_reference.xor
      (pack a0 a1 a2 a3) (pack b0 b1 b2 b3) =
      ok (pack (a0 ^^^ b0) (a1 ^^^ b1) (a2 ^^^ b2) (a3 ^^^ b3)) := by
  simp only [PV_CBL_FallbackSchedule.sha_fallback_reference.xor,index0,index1,index2,index3,lift,bind_tc_ok]
  rfl
#print axioms shape
end R1Z.PV_CBL_FallbackLaneXor
