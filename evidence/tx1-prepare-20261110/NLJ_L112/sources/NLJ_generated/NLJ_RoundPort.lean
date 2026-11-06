import NLJ_InstalledBoundaries
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLJ_RoundPort
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
/-- Focused test of the136 packet's round interpretation against the installed
prepare wrapper. A failed definition-equality test is not a counterexample. -/
theorem rounds : NJM_RoundJoin.R = AspisS1ExtractedRoundChildren.children := rfl
#print axioms rounds
end AspisR1.NLJ_RoundPort
end
