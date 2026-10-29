import R1Z.PV_RDB2E_FallbackLanes

section
-- Unchanged source component R1Z.PV_CBL_FallbackMessage1
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_FallbackMessage1
open PV_CBL_FallbackArray4 PV_CBL_FallbackSmallSigma
set_option autoImplicit false
theorem shape (a0 a1 a2 a3 b0 b1 b2 b3 : U32) :
    PV_CBL_FallbackSchedule.sha_fallback_reference.sha256msg1
      (pack a0 a1 a2 a3) (pack b0 b1 b2 b3) =
      ok (pack (U32.wrapping_add a0 (small0 b3)) (U32.wrapping_add a1 (small0 a0))
        (U32.wrapping_add a2 (small0 a1)) (U32.wrapping_add a3 (small0 a2))) := by
  simp only [PV_CBL_FallbackSchedule.sha_fallback_reference.sha256msg1,
    PV_CBL_FallbackLaneLoad.shape,sigma0_shape,PV_CBL_FallbackLaneAdd.shape,lift,bind_tc_ok]
#print axioms shape
end R1Z.PV_CBL_FallbackMessage1

end
