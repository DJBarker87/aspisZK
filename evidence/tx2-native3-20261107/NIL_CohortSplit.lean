import NIL_ResumeCohortTail
import NIL_SpineCongr
set_option autoImplicit false
noncomputable section
namespace NIL_CohortSplit
open Aeneas Aeneas.Std Result AspisR1Stage2

theorem source (ops : ResumeOps) {H : Type} (d : aspis_core.digest.Digest32 H)
 (bytes proof public1 : Slice U8) (v : transport.Variant) (hash : H) :
 verifier.resumeWithOps ops d bytes proof public1 v hash=
 NIL_ResumePrefixCut.cohort ops d bytes proof public1 v hash
 (NIL_ResumeCohortTail.tail ops bytes v) := by
 unfold verifier.resumeWithOps NIL_ResumePrefixCut.cohort NIL_ResumeCohortTail.tail
 repeat' first
  | (with_unfolding_all apply NIL_ResultCases.bind_congr; intro x)
  | apply NIL_ResultCases.branch_congr
  | (with_unfolding_all apply NIL_SpineCongr.prod; intro x y)
  | rfl
  | (cases x <;> rename_i x)
#print axioms source
end NIL_CohortSplit
