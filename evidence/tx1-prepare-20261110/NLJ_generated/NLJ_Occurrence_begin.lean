import NLJ_ObservedWindows
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLJ_Observed
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
/-- One exact source occurrence. Native carry is a separate reviewed cut. -/
theorem occurrence_begin {H : Type} (s : State H) (p : r1_wire.Prefix) (t : r1_wire.SemanticTranscript H)
 (atSite : s.locals = .begin p t) : step s = beginWindow s p t := by
 simp only [step,atSite]
 try rfl
#print axioms occurrence_begin
end AspisR1.NLJ_Observed
end
