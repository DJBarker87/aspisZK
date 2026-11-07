import NLU_StepProjection
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLU
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
/-- Explicit per-occurrence G action: caller source slots plus linear-owner
bookkeeping. Native provenance is required separately for every occurrence. -/
def execute {H : Type} (s : NLU.State H) (code : PreparedHashCode.Code (NLC_Finish.Post H)) : StepObservation H :=
 let head:=PreparedHashCode.run code
 let events:=entered s ++ head.1.map NLU.Event.digest
 match head.2 with
 | .fail err=>⟨s.machine.input,events,.fail err⟩
 | .div=>⟨s.machine.input,events,.div⟩
 | .ok post=>let next:=carry s post;⟨s.machine.input,events++next.1,.ok next.2⟩
theorem execute_step {H : Type} (s : NLU.State H) : step s=execute s (NLC_Finish.step s.machine) := rfl
#print axioms execute_step
end AspisR1.NLU
end
