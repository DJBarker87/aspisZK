import NLJ_ObservedInvariants
import NLJ_Occurrence_mark0
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLJ_Observed
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
/-- Arbitrary-reply frame for this source occurrence, not a native cut. -/
theorem frame_mark0 {H : Type} (s : State H) (p : r1_wire.Prefix)
 (atSite : s.locals = .mark0 p) : NLC_Finish.AllLeaves (FramePost s) (step s) := by
 rw [occurrence_mark0 s p atSite]
 repeat' first
 | (apply NLC_Finish.all_bind; intro)
 | (change ∀ _, _; intro)
 | (change True; trivial)
 | split
 all_goals rfl
#print axioms frame_mark0
end AspisR1.NLJ_Observed
end
