-- Inherited body, import-only deployed-cohort retarget.
import NCD_B_NBQ_Filled
set_option autoImplicit false
namespace NCB_ResizeStep
open Aeneas Aeneas.Std Result
/-- One standard-library model initialization step, preserving all prior
contents. This is not a native ownership theorem. -/
theorem next {T : Type} (clone : core.clone.Clone T) (before : alloc.vec.Vec T)
    (n : Usize) (value : T) (hn : n.val=before.val.length+1)
    (copy : clone.clone value=ok value) :
    ∃ after, alloc.vec.Vec.resize clone before n value=ok after ∧
      after.val=before.val++[value] := by
  obtain ⟨after,run,contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.resize_spec clone before n value copy)
  refine ⟨after,run,?_⟩
  rw [contents]
  simp [List.resize,hn]
#print axioms next
end NCB_ResizeStep
