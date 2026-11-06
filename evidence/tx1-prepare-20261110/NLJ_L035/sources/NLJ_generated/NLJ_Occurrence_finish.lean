import NLJ_ObservedWindows
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLJ_Observed
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
/-- One exact source occurrence. Native carry is a separate reviewed cut. -/
theorem occurrence_finish {H : Type} (s : State H) (p : r1_wire.Prefix) (t : r1_wire.SemanticTranscript H) (c : r1_wire.Challenges)
 (atSite : s.locals = .finish p t c) : step s = (do let r ← S1SemanticCode.finish NJM_RoundJoin.R (IDa_Deployed.boundaries s.input.reservation) s.input.digest s.input.publicValue p t c none; pure (.inl r)) := by
 simp only [step,atSite]
 try rfl
#print axioms occurrence_finish
end AspisR1.NLJ_Observed
end
