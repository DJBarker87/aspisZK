import NLJ_ObservedWindows
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLJ_Observed
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
/-- One exact source occurrence. Native carry is a separate reviewed cut. -/
theorem occurrence_mark0 {H : Type} (s : State H) (p : r1_wire.Prefix)
 (atSite : s.locals = .mark0 p) : step s = (do VerifyPrefix.mark none 0#u8; pure (.inr (advance s (.publicTranscript p)))) := by
 simp only [step,atSite]
 try rfl
#print axioms occurrence_mark0
end AspisR1.NLJ_Observed
end
