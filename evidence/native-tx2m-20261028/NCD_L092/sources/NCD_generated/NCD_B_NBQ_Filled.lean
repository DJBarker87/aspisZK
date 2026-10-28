-- Inherited body, import-only deployed-cohort retarget.
import NCD_B_NBC_Filled
set_option autoImplicit false
noncomputable section
namespace NBQ_Filled
open Aeneas Aeneas.Std Result AspisR1 AspisR1ClaimsUnrolledParent AspisR1.NP6_StdModel
/-- Arbitrary size, not a bounded native allocation fixture. Reservation is
exactly the runtime allocator reply; copy is the pinned Copy implementation. -/
theorem returned {T : Type} (copy : core.marker.Copy T) (n : Usize) (value : T)
    (cloned : copy.cloneInst.clone value = ok value) :
    aspis_core.r0.heap.filled (ClaimsUnrolledFinish.external (calls (.Ok ()))) copy n value =
      ok (.Ok (⟨List.replicate n.val value, by simp; scalar_tac⟩ : alloc.vec.Vec T)) :=
  NBC_Filled.result (.Ok ()) copy n value cloned
/-- Every selected element is initialized, including at arbitrary positive
sizes. No copy builtin or concrete buffer enumeration is evaluated. -/
theorem selected {T : Type} (n : Nat) (value : T) (i : Nat) (hi : i<n) :
    (List.replicate n value)[i]? = some value := by
  simp [hi]
#print axioms returned
#print axioms selected
end NBQ_Filled
