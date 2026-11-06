import NLJ_ObservedInvariants
import NLJ_Occurrence_publicTranscript
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLJ_Observed
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
/-- Arbitrary-reply frame for this source occurrence, not a native cut. -/
theorem frame_publicTranscript {H : Type} (s : State H) (p : r1_wire.Prefix)
 (atSite : s.locals = .publicTranscript p) : NLC_Finish.AllLeaves (FramePost s) (step s) := by
 rw [occurrence_publicTranscript s p atSite]
 unfold publicWindow
 repeat' first
 | (apply NLC_Finish.all_bind; intro)
 | (change ∀ _, _; intro)
 | (change True; trivial)
 | split
 all_goals rfl
#print axioms frame_publicTranscript
end AspisR1.NLJ_Observed
end
