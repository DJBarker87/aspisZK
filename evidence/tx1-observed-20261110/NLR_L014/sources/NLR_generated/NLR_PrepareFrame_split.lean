import NLR_PrepareDenote
import NLJ_PrepareWindow_split
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLR_Prepare
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open AspisR1PublicPreparation.PreparedHashCode (Code run)
open NLJ_Prepare
theorem frame_split  (cfg : Configuration) {H : Type} (s : State H) (n : Usize) (logical : alloc.vec.Vec U8)
 (atSite : s.locals = .split n logical) : NLC_Finish.AllLeaves (FramePost s) (step cfg s) := by
 rw [step_split cfg s n logical atSite]
 unfold window_split
 repeat' first
 | (apply NLC_Finish.all_bind; intro)
 | (change ∀ _, _; intro)
 | (change True; trivial)
 | split
 all_goals rfl
#print axioms frame_split
end AspisR1.NLR_Prepare
end
