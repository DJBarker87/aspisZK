import SCE_Experiment
set_option autoImplicit false
namespace AspisR1.SCE_SubmissionExt
open F3T_ByteCarrier
/-- Keep large native byte carriers opaque when proving submission equality. -/
theorem equal (left right : Submission)
    (publicBytes : left.publicBytes = right.publicBytes)
    (stored : left.stored = right.stored) : left = right := by
  cases left
  cases right
  cases publicBytes
  cases stored
  rfl
#print axioms equal
end AspisR1.SCE_SubmissionExt
