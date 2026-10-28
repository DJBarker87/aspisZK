import NBC_Filled
set_option autoImplicit false
noncomputable section
namespace NBP_FilledPorts
open Aeneas Aeneas.Std Result AspisR1 AspisR1ClaimsUnrolledParent AspisR1.NP6_StdModel
/-- All allocation errors retain the selected Allocation result. This reuses
NBC's complete model law; it does not assert native reservation fidelity. -/
theorem allocation {T : Type} (copy : core.marker.Copy T) (n : Usize) (value : T)
    (cloned : copy.cloneInst.clone value = ok value) (error : ReserveError) :
    aspis_core.r0.heap.filled (ClaimsUnrolledFinish.external (calls (.Err error))) copy n value =
      ok (.Err .Allocation) := by
  exact NBC_Filled.result (.Err error) copy n value cloned
theorem zero {T : Type} (copy : core.marker.Copy T) (value : T)
    (cloned : copy.cloneInst.clone value = ok value) :
    aspis_core.r0.heap.filled (ClaimsUnrolledFinish.external (calls (.Ok ()))) copy 0#usize value =
      ok (.Ok (⟨[],by simp⟩ : alloc.vec.Vec T)) := by
  exact NBC_Filled.result (.Ok ()) copy 0#usize value cloned
#print axioms zero
#print axioms allocation
end NBP_FilledPorts
