import NLJ_ObservedInvariants
import NLJ_Occurrence_begin
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLJ_Observed
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
/-- Arbitrary-reply frame for this source occurrence, not a native cut. -/
theorem frame_begin {H : Type} (s : State H) (p : r1_wire.Prefix) (t : r1_wire.SemanticTranscript H)
 (atSite : s.locals = .begin p t) : NLC_Finish.AllLeaves (FramePost s) (step s) := by
 rw [occurrence_begin s p t atSite]
 unfold beginWindow
 repeat' first
 | (apply NLC_Finish.all_bind; intro)
 | (change ∀ _, _; intro)
 | (change True; trivial)
 | split
 all_goals rfl
#print axioms frame_begin
end AspisR1.NLJ_Observed
end
