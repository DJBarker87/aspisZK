import NLR_PrepareDenote
import NLJ_PrepareWindow_allocate
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLR_Prepare
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open AspisR1PublicPreparation.PreparedHashCode (Code run)
open NLJ_Prepare
theorem frame_allocate  (cfg : Configuration) {H : Type} (s : State H) 
 (atSite : s.locals = .allocate ) : NLC_Finish.AllLeaves (FramePost s) (step cfg s) := by
 rw [step_allocate cfg s  atSite]
 unfold window_allocate
 repeat' first
 | (apply NLC_Finish.all_bind; intro)
 | (change ∀ _, _; intro)
 | (change True; trivial)
 | split
 all_goals rfl
#print axioms frame_allocate
end AspisR1.NLR_Prepare
end
