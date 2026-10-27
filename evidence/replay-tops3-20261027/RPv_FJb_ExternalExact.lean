import RPv_FJb_ExternalModel
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJb_ExternalExact
open Aeneas Aeneas.Std Result FIq_Native
open FIw_ArrayValue (canonical decoded)
open FJb_MatrixGroupStep (State)
/-- Native external-linear refinement to the retained exact literal model. -/
theorem value (s out : State) (hs : canonical s)
    (run : state_only_poseidon.external_linear_lazy s=ok out) :
    canonical out ∧ decoded out=R0P.poseidonExternalLinear (decoded s) := by
  have v := FJb_ExternalValue.value s out hs run
  exact ⟨v.1,v.2.trans (FJb_ExternalModel.value _)⟩
#print axioms value
end AspisR1.FJb_ExternalExact
end
