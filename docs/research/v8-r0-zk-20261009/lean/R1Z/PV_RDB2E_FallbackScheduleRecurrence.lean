import R1Z.PV_RDB2E_FallbackScheduleShape

section
-- Unchanged source component R1Z.PV_CBL_FallbackScheduleRecurrence
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_FallbackScheduleRecurrence
open PV_CBL_FallbackArray4 PV_CBL_FallbackSmallSigma
set_option autoImplicit false
/-- SHA-256's word recurrence, in the source's wrapping-add order. -/
def next (a b c d : U32) : U32 :=
  U32.wrapping_add (U32.wrapping_add (U32.wrapping_add a (small0 b)) c) (small1 d)
theorem four (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : U32) :
    PV_CBL_FallbackSchedule.sha_fallback_reference.extracted_schedule
      (pack w3 w2 w1 w0) (pack w7 w6 w5 w4) (pack w11 w10 w9 w8) (pack w15 w14 w13 w12) =
      let w16 := next w0 w1 w9 w14
      let w17 := next w1 w2 w10 w15
      let w18 := next w2 w3 w11 w16
      let w19 := next w3 w4 w12 w17
      ok (pack w19 w18 w17 w16) := by
  exact PV_CBL_FallbackScheduleShape.shape _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
#print axioms next
#print axioms four
end R1Z.PV_CBL_FallbackScheduleRecurrence

end
