-- Inherited body, import-only deployed-cohort retarget.
import RPz7_NP6_ClaimsModel
set_option autoImplicit false
noncomputable section
namespace NBC_Filled
open Aeneas Aeneas.Std Result
open AspisR1 AspisR1ClaimsUnrolledParent AspisR1.NP6_StdModel

/-- Reuse the complete existing pure std value law, retaining allocation
failure and deriving contents rather than assuming successful filled output.
Native std/allocator/ownership association is expressly outside this theorem. -/
theorem result (reservation : Reservation) {T : Type}
    (copy : core.marker.Copy T) (n : Usize) (value : T)
    (cloned : copy.cloneInst.clone value = ok value) :
    aspis_core.r0.heap.filled (ClaimsUnrolledFinish.external (calls reservation)) copy n value =
      match reservation with
      | .Err _ => ok (.Err .Allocation)
      | .Ok () => ok (.Ok (⟨List.replicate n.val value, by simp; scalar_tac⟩ : alloc.vec.Vec T)) :=
  AspisR1.NP6_ClaimsModel.filled_contents reservation copy n value cloned

#print axioms result
end NBC_Filled
