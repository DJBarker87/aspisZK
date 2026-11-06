import NLR_PrepareDenote
import NLJ_PrepareWindow_mapSemantic
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLR_Prepare
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open AspisR1PublicPreparation.PreparedHashCode (Code run)
open NLJ_Prepare
theorem frame_mapSemantic  (cfg : Configuration) {H : Type} (s : State H) (logical : alloc.vec.Vec U8) (v : verifier.View) (r : core.result.Result (r1_semantic.Verified H) r1_wire.Error)
 (atSite : s.locals = .mapSemantic logical v r) : NLC_Finish.AllLeaves (FramePost s) (step cfg s) := by
 rw [step_mapSemantic cfg s logical v r atSite]
 unfold window_mapSemantic
 repeat' first
 | (apply NLC_Finish.all_bind; intro)
 | (change ∀ _, _; intro)
 | (change True; trivial)
 | split
 all_goals rfl
#print axioms frame_mapSemantic
end AspisR1.NLR_Prepare
end
