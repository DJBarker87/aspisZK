import NLR_PrepareDenote
import NLJ_PrepareWindow_expandSemantic
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLR_Prepare
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open AspisR1PublicPreparation.PreparedHashCode (Code run)
open NLJ_Prepare
theorem frame_expandSemantic  (cfg : Configuration) {H : Type} (s : State H) (n offY1 : Usize) (semantic y1 compressed : Slice U8) (splitBack : SplitBack) (vecBack : VecBack)
 (atSite : s.locals = .expandSemantic n offY1 semantic y1 compressed splitBack vecBack) : NLC_Finish.AllLeaves (FramePost s) (step cfg s) := by
 rw [step_expandSemantic cfg s n offY1 semantic y1 compressed splitBack vecBack atSite]
 unfold window_expandSemantic
 repeat' first
 | (apply NLC_Finish.all_bind; intro)
 | (change ∀ _, _; intro)
 | (change True; trivial)
 | split
 all_goals rfl
#print axioms frame_expandSemantic
end AspisR1.NLR_Prepare
end
