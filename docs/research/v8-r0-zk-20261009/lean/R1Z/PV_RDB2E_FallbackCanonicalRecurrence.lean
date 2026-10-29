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
