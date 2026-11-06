import NLJ_ObservedWindows
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLJ_Observed
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
/-- One exact source occurrence. Native carry is a separate reviewed cut. -/
theorem occurrence_mark1 {H : Type} (s : State H) (p : r1_wire.Prefix) (t : r1_wire.SemanticTranscript H) (c : r1_wire.Challenges)
 (atSite : s.locals = .mark1 p t c) : step s = (do VerifyPrefix.mark none 1#u8; pure (.inr (advance s (.finish p t c)))) := by
 simp only [step,atSite]
 try rfl
#print axioms occurrence_mark1
end AspisR1.NLJ_Observed
end
