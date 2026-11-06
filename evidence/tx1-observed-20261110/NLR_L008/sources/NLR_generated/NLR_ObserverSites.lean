import NLJ_ObservedStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLR_ObserverSites
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (run)
/-- Exact source0 marker site: all Prefix fields and complete input retained.
Native None-valued pointer comparisons are deliberately absent. Native
admission still requires the deployed-feature source erasure certificate. -/
theorem mark0 {H : Type} (i : NLJ_Observed.Input H) (p : r1_wire.Prefix) :
 run (NLJ_Observed.step ⟨i,.mark0 p⟩) =
 ([],ok (.inr ⟨i,.publicTranscript p⟩)) := rfl
/-- Exact source1 marker site, including post-begin transcript/challenges. -/
theorem mark1 {H : Type} (i : NLJ_Observed.Input H) (p : r1_wire.Prefix)
 (t : r1_wire.SemanticTranscript H) (c : r1_wire.Challenges) :
 run (NLJ_Observed.step ⟨i,.mark1 p t c⟩) =
 ([],ok (.inr ⟨i,.finish p t c⟩)) := rfl
#print axioms mark0
#print axioms mark1
end AspisR1.NLR_ObserverSites
end
