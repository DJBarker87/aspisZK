import NLR_PrepareDenote
import NLJ_PrepareWindow_mark
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLR_Prepare
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open AspisR1PublicPreparation.PreparedHashCode (Code run)
open NLJ_Prepare
theorem frame_mark  (cfg : Configuration) {H : Type} (s : State H) (logical : alloc.vec.Vec U8) (v : verifier.View) (sem : r1_semantic.Verified H)
 (atSite : s.locals = .mark logical v sem) : NLC_Finish.AllLeaves (FramePost s) (step cfg s) := by
 rw [step_mark cfg s logical v sem atSite]
 unfold window_mark
 repeat' first
 | (apply NLC_Finish.all_bind; intro)
 | (change ∀ _, _; intro)
 | (change True; trivial)
 | split
 all_goals rfl
#print axioms frame_mark
end AspisR1.NLR_Prepare
end
