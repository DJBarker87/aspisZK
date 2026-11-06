import NLR_PrepareDenote
import NLJ_PrepareWindow_view
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLR_Prepare
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open AspisR1PublicPreparation.PreparedHashCode (Code run)
open NLJ_Prepare
theorem frame_view  (cfg : Configuration) {H : Type} (s : State H) (logical : alloc.vec.Vec U8) (semantic y1 : Slice U8)
 (atSite : s.locals = .view logical semantic y1) : NLC_Finish.AllLeaves (FramePost s) (step cfg s) := by
 rw [step_view cfg s logical semantic y1 atSite]
 unfold window_view
 repeat' first
 | (apply NLC_Finish.all_bind; intro)
 | (change ∀ _, _; intro)
 | (change True; trivial)
 | split
 all_goals rfl
#print axioms frame_view
end AspisR1.NLR_Prepare
end
