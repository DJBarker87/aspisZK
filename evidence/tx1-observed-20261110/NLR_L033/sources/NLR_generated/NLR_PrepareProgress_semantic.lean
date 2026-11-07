import NLR_PrepareDenote
import NLJ_PrepareWindow_semantic
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLR_Prepare
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open AspisR1PublicPreparation.PreparedHashCode (Code run)
open NLJ_Prepare
theorem progress_semantic  (cfg : Configuration) {H : Type} (s : State H) (logical : alloc.vec.Vec U8) (v : verifier.View)
 (atSite : s.locals = .semantic logical v) : NLC_Finish.AllLeaves (ProgressPost s) (step cfg s) := by
 rw [step_semantic cfg s logical v atSite]
 unfold window_semantic
 repeat' first
 | (apply NLC_Finish.all_bind; intro)
 | (change ∀ _, _; intro)
 | (change True; trivial)
 | split
 all_goals change rank _ < rank s
 all_goals simp only [rank,advance,atSite]
 all_goals decide
#print axioms progress_semantic
end AspisR1.NLR_Prepare
end
