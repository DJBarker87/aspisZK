import NLR_PrepareDenote
import NLJ_PrepareWindow_constructor
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLR_Prepare
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open AspisR1PublicPreparation.PreparedHashCode (Code run)
open NLJ_Prepare
theorem frame_constructor  (cfg : Configuration) {H : Type} (s : State H) (logical : alloc.vec.Vec U8) (v : verifier.View) (sem : r1_semantic.Verified H)
 (atSite : s.locals = .constructor logical v sem) : NLC_Finish.AllLeaves (FramePost s) (step cfg s) := by
 rw [step_constructor cfg s logical v sem atSite]
 unfold window_constructor
 repeat' first
 | (apply NLC_Finish.all_bind; intro)
 | (change ∀ _, _; intro)
 | (change True; trivial)
 | split
 all_goals rfl
#print axioms frame_constructor
end AspisR1.NLR_Prepare
end
