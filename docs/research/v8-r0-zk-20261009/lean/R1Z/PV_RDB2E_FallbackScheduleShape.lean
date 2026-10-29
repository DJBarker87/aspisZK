import R1Z.PV_RDB2E_FallbackMessage1
import R1Z.PV_RDB2E_FallbackMessage2

section
-- Unchanged source component R1Z.PV_CBL_FallbackScheduleShape
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_FallbackScheduleShape
open PV_CBL_FallbackArray4 PV_CBL_FallbackSmallSigma
set_option autoImplicit false
theorem shape (a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 d0 d1 d2 d3 : U32) :
    PV_CBL_FallbackSchedule.sha_fallback_reference.extracted_schedule
      (pack a0 a1 a2 a3) (pack b0 b1 b2 b3) (pack c0 c1 c2 c3) (pack d0 d1 d2 d3) =
      let t0 := U32.wrapping_add (U32.wrapping_add a0 (small0 b3)) d3
      let t1 := U32.wrapping_add (U32.wrapping_add a1 (small0 a0)) c0
      let t2 := U32.wrapping_add (U32.wrapping_add a2 (small0 a1)) c1
      let t3 := U32.wrapping_add (U32.wrapping_add a3 (small0 a2)) c2
      let w0 := U32.wrapping_add t3 (small1 d1)
      let w1 := U32.wrapping_add t2 (small1 d0)
      let w2 := U32.wrapping_add t1 (small1 w0)
      let w3 := U32.wrapping_add t0 (small1 w1)
      ok (pack w3 w2 w1 w0) := by
  simp only [PV_CBL_FallbackSchedule.sha_fallback_reference.extracted_schedule,
    PV_CBL_FallbackSchedule.sha_fallback_reference.schedule,
    PV_CBL_FallbackMessage1.shape,PV_CBL_FallbackMessage2.shape,
    PV_CBL_FallbackLaneLoad.shape,PV_CBL_FallbackLaneAdd.shape,lift,bind_tc_ok]
#print axioms shape
end R1Z.PV_CBL_FallbackScheduleShape

end
