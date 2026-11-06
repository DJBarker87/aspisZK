import NLJ_ObservedWindows
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLJ_Observed
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
/-- One exact source occurrence. Native carry is a separate reviewed cut. -/
theorem occurrence_publicTranscript {H : Type} (s : State H) (p : r1_wire.Prefix)
 (atSite : s.locals = .publicTranscript p) : step s = publicWindow s p := by
 simp only [step,atSite]
 try rfl
#print axioms occurrence_publicTranscript
end AspisR1.NLJ_Observed
end
