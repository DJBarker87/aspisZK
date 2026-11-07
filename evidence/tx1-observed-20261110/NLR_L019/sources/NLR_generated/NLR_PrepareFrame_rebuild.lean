import NLR_PrepareDenote
import NLJ_PrepareWindow_rebuild
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLR_Prepare
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open AspisR1PublicPreparation.PreparedHashCode (Code run)
open NLJ_Prepare
theorem frame_rebuild  (cfg : Configuration) {H : Type} (s : State H) (n : Usize) (semantic y1 : Slice U8) (splitBack : SplitBack) (vecBack : VecBack)
 (atSite : s.locals = .rebuild n semantic y1 splitBack vecBack) : NLC_Finish.AllLeaves (FramePost s) (step cfg s) := by
 rw [step_rebuild cfg s n semantic y1 splitBack vecBack atSite]
 unfold window_rebuild
 repeat' first
 | (apply NLC_Finish.all_bind; intro)
 | (change ∀ _, _; intro)
 | (change True; trivial)
 | split
 all_goals rfl
#print axioms frame_rebuild
end AspisR1.NLR_Prepare
end
