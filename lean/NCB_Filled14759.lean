import NBQ_Filled
import NBS_FilledTrace
import NCB_ResizeStep
set_option autoImplicit false
noncomputable section
namespace NCB_Filled14759
open Aeneas Aeneas.Std Result AspisR1 AspisR1ClaimsUnrolledParent AspisR1.NP6_StdModel
/-- Exact preparation size, using the inherited model law. Native allocation
ownership and lifetime are not inferred from this model instance. -/
theorem model {T : Type} (copy : core.marker.Copy T) (value : T)
    (cloned : copy.cloneInst.clone value=ok value) :
    aspis_core.r0.heap.filled (ClaimsUnrolledFinish.external (calls (.Ok ())))
      copy 14759#usize value =
      ok (.Ok (⟨List.replicate 14759 value,by simp only [List.length_replicate];scalar_tac⟩ : alloc.vec.Vec T)) :=
  NBQ_Filled.returned copy 14759#usize value cloned
/-- Selected bytes of the exact same model carrier; no enumeration. -/
theorem selected {T : Type} (value : T) (i : Nat) (bound : i<14759) :
    (List.replicate 14759 value)[i]?=some value :=
  NBQ_Filled.selected 14759 value i bound
#print axioms model
#print axioms selected
end NCB_Filled14759
