import R1Z.PV_RDB2E_FallbackRotate
import R1Z.PV_RDB2E_FallbackCanonical
import R1Z.PV_RDB2E_FallbackScheduleRecurrence

section
-- Unchanged source component R1Z.PV_CBL_FallbackCanonicalRecurrence
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_FallbackCanonicalRecurrence
open PV_CBL_FallbackSmallSigma
set_option autoImplicit false
abbrev sigma0 (x : U32) : U32 :=
  core.num.U32.rotate_right x 7#u32 ^^^ core.num.U32.rotate_right x 18#u32 ^^^ U32.wrapping_shr x 3#u32
abbrev sigma1 (x : U32) : U32 :=
  core.num.U32.rotate_right x 17#u32 ^^^ core.num.U32.rotate_right x 19#u32 ^^^ U32.wrapping_shr x 10#u32
def next (w0 w1 w9 w14 : U32) : U32 :=
  U32.wrapping_add (U32.wrapping_add (U32.wrapping_add (sigma1 w14) w9) (sigma0 w1)) w0
theorem source_next (w0 w1 w9 w14 : U32) :
    PV_CBL_FallbackScheduleRecurrence.next w0 w1 w9 w14 = next w0 w1 w9 w14 := by
  unfold PV_CBL_FallbackScheduleRecurrence.next next
  rw [PV_CBL_FallbackRotate.small0_eq]
  exact PV_CBL_FallbackAddAlgebra.reverse4 _ _ _ _
#print axioms sigma0
#print axioms sigma1
#print axioms next
#print axioms source_next
end R1Z.PV_CBL_FallbackCanonicalRecurrence

end

section
-- Unchanged source component R1Z.PV_CBL_FallbackScheduleCanonical
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_FallbackScheduleCanonical
open PV_CBL_FallbackArray4 PV_CBL_FallbackCanonicalRecurrence
set_option autoImplicit false
theorem source (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : U32) :
    PV_CBL_FallbackSchedule.sha_fallback_reference.extracted_schedule
      (pack w3 w2 w1 w0) (pack w7 w6 w5 w4) (pack w11 w10 w9 w8) (pack w15 w14 w13 w12) =
      let w16 := next w0 w1 w9 w14
      let w17 := next w1 w2 w10 w15
      let w18 := next w2 w3 w11 w16
      let w19 := next w3 w4 w12 w17
      ok (pack w19 w18 w17 w16) := by
  simpa only [PV_CBL_FallbackCanonicalRecurrence.source_next] using
    PV_CBL_FallbackScheduleRecurrence.four w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
#print axioms source
end R1Z.PV_CBL_FallbackScheduleCanonical

end
