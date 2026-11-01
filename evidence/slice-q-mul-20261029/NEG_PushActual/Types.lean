import NEG_RowIsolated.Types
import Port23PUSH_Source
namespace NEG_PushActual
open Aeneas Aeneas.Std
abbrev aspis_core.field.M31 := U32
abbrev aspis_core.field.CM31 := NEG_RowIsolated.aspis_core.field.CM31
abbrev aspis_core.field.QM31 := NEG_RowIsolated.aspis_core.field.QM31
/-- Reuse the cohort record carrier; fields match the generated type exactly. -/
abbrev BatchedWeights := Port23PUSH.verifier.BatchedWeights
 theorem carrier (b : BatchedWeights) :
    (⟨b.raw,b.terms⟩ : Port23PUSH.verifier.BatchedWeights) = b := by cases b; rfl
#print axioms carrier
end NEG_PushActual
